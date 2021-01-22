//! Helper crate for [lemon-tree](https://crates.io/crates/lemon-tree). Rust-way parser builder.

#![feature(proc_macro_span)]

extern crate lemon_mint;
extern crate proc_macro;
extern crate proc_macro2;
extern crate once_cell;

use std::mem;
use std::collections::{HashSet, HashMap, hash_map::DefaultHasher};
use std::hash::{Hash, Hasher};
use std::sync::{Mutex, Arc};
use std::time::SystemTime;
use syn::{self, DeriveInput, Data, Attribute, Meta, NestedMeta, Lit, Ident, ItemFn, ReturnType, Type, TypePath, Path, PathSegment, PathArguments, FnArg, PatType, Pat};
use crate::proc_macro::TokenStream;
use crate::proc_macro2::Span;
use quote::quote;
use once_cell::sync::OnceCell;
use lemon_mint::LemonMintBuilder;
use std::borrow::Cow;
use std::fmt::Write;

static DERIVE: OnceCell<Derive> = OnceCell::new();

/// Makes enum/struct a start symbol of current parser. Must appear the last parser attribute in file.
#[proc_macro_derive(LemonTree, attributes(lem, lem_opt))]
pub fn derive_lemon_tree(input: TokenStream) -> TokenStream
{	match DERIVE.get_or_init(|| Default::default()).derive(input, true)
	{	Ok(ts) => ts,
		Err(error) => panic!(error),
	}
}

/// Makes enum/struct a regular nonterminal symbol. Must appear before `#[derive(LemonTree)]` and `#[lem_fn()]` in the same rust file.
#[proc_macro_derive(LemonTreeNode, attributes(lem))]
pub fn derive_lemon_tree_node(input: TokenStream) -> TokenStream
{	match DERIVE.get_or_init(|| Default::default()).derive(input, false)
	{	Ok(ts) => ts,
		Err(error) => panic!(error),
	}
}

/// Makes module-global public function an action for specified Lemon parser expression.
#[proc_macro_attribute]
pub fn lem_fn(attr: TokenStream, item: TokenStream) -> TokenStream
{	match DERIVE.get_or_init(|| Default::default()).lem_fn_attr(attr, item)
	{	Ok(item) => item,
		Err(error) => panic!(error),
	}
}

struct Alts
{	alts: Vec<String>,
	split_points: Vec<usize>,
}
impl Alts
{	pub fn split(mut value: &str, output: &mut Vec<String>) -> Result<(), String>
	{	let mut this = Self
		{	alts: vec![String::with_capacity(value.len())],
			split_points: vec![1],
		};
		value = value.trim();
		while value.len() != 0
		{	let pos = value.bytes().position(|c| c==b'[' || c==b']').unwrap_or(value.len());
			this.push_str(&value[.. pos]);
			if pos == value.len()
			{	break;
			}
			if value.as_bytes()[pos] == b'['
			{	this.opt_start();
			}
			else
			{	this.opt_end()?;
			}
			value = &value[pos+1 ..];
		}
		if this.split_points.len() != 1
		{	return Err(format!("Square bracket not closed"));
		}
		output.extend_from_slice(&this.alts);
		Ok(())
	}

	fn push_str(&mut self, s: &str)
	{	let active = self.split_points[0];
		let from = self.alts.len() - active;
		for a in &mut self.alts[from ..]
		{	a.push_str(s);
		}
	}

	fn opt_start(&mut self)
	{	let active = self.split_points[0];
		self.alts.reserve(active);
		for i in self.alts.len()-active .. self.alts.len()
		{	self.alts.push(self.alts[i].clone());
		}
		self.split_points.push(self.alts.len());
	}

	fn opt_end(&mut self) -> Result<(), String>
	{	if self.split_points.len() <= 1
		{	return Err(format!("Unbalanced square brackets"));
		}
		self.split_points.remove(0);
		Ok(())
	}
}

enum CurBuilder
{	Active(LemonMintBuilder, String), // (builder, grammar)
	Complete(usize), // line where start symbol occured
}

#[derive(Copy, Clone, Hash, PartialEq, Eq)]
struct Ns
{	hash: u64,
	is_real_file: bool,
}

#[derive(Default)]
struct Derive
{	builders: Mutex<HashMap<Ns, CurBuilder>>,
	filenames: Mutex<HashSet<Arc<String>>>,
	last_use: Mutex<HashMap<Ns, (SystemTime, usize)>>,
}

impl Derive
{	pub fn derive(&self, input: TokenStream, is_start_symbol: bool) -> Result<TokenStream, String>
	{	let (ns, filename, n_line) = self.get_location(input.clone())?;
		self.reinit_if_needed(ns, n_line);
		let ast: &DeriveInput = &syn::parse(input).unwrap();
		let name = &ast.ident;
		self.add_type(ns, &filename, n_line, name.to_string(), false)?;
		self.parse_lem_opt_attrs(ns, &filename, n_line, &ast.attrs)?;
		match &ast.data
		{	Data::Enum(data_enum) =>
			{	for variant in &data_enum.variants
				{	let variant_name = &variant.ident;
					for value in Self::parse_lem_attrs(&variant.attrs).map_err(|e| format!("In enum variant {}: {}", variant.ident, e))?
					{	if !value.trim().is_empty()
						{	let (value, aliases) = Self::parse_rhs(&value, variant.fields.len(), None, false).map_err(|e| format!("In enum variant {}: {}", variant.ident, e))?;
							let mut action = quote!();
							for i in 0 .. variant.fields.len()
							{	if aliases.iter().position(|&a| a==i).is_some()
								{	let arg = Ident::new(&format!("arg_{}", i), Span::call_site());
									action = quote!(#action #arg.into(),);
								}
								else
								{	action = quote!(#action std::default::Default::default(),);
								}
							}
							if variant.fields.len() > 0
							{	action = quote!((#action));
							}
							self.add_rule(ns, &filename, n_line, name.to_string(), value, quote!(super::super::#name::#variant_name #action).to_string()).map_err(|e| format!("In enum variant {}: {}", variant.ident, e))?;
						}
					}
				}
			}
			Data::Struct(data_struct) =>
			{	for value in Self::parse_lem_attrs(&ast.attrs)?
				{	if !value.trim().is_empty()
					{	let mut field_names = Vec::with_capacity(data_struct.fields.len());
						let mut field_names_str = Vec::with_capacity(data_struct.fields.len());
						for field in data_struct.fields.iter()
						{	if let Some(ref field_name) = field.ident
							{	field_names_str.push(field_name.to_string());
								field_names.push(field_name);
							}
						}
						let (value, aliases) = Self::parse_rhs(&value, field_names_str.len(), Some(&field_names_str), false)?;
						let mut action = quote!();
						let mut comma = false;
						for (i, field_name) in field_names.into_iter().enumerate()
						{	if aliases.iter().position(|&n| i==n).is_some()
							{	if comma
								{	action = quote!(#action,);
								}
								comma = true;
								action = quote!(#action #field_name: #field_name.into());
							}
							else
							{	if comma
								{	action = quote!(#action,);
								}
								comma = true;
								action = quote!(#action #field_name: std::default::Default::default());
							}
						}
						action = quote!(super::super::#name {#action});
						self.add_rule(ns, &filename, n_line, name.to_string(), value, action.to_string())?;
					}
				}
			},
			Data::Union(_data_union) =>
			{	return Err("Not implemented".to_string());
			},
		}
		let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
		let mut code = quote!
		{	impl #impl_generics lemon_tree::LemonTreeNode for #name #ty_generics #where_clause
			{
			}
		};
		if is_start_symbol
		{	let rust = self.get_lemon_result(ns, &filename, n_line, name.to_string())?;
			let rust: proc_macro2::TokenStream = rust.parse().unwrap();
			let ns_name = Ident::new(&format!("lem_{}", ns.hash), Span::call_site());
			code = quote!
			{	#code
				impl #impl_generics lemon_tree::LemonTree for #name #ty_generics #where_clause
				{	type Token = #ns_name::code::Token;
					type Parser = #ns_name::code::Parser;
				}
				impl #impl_generics #name #ty_generics #where_clause
				{	fn get_parser(extra: #ns_name::code::ExtraArgumentType) -> #ns_name::code::Parser
					{	#ns_name::code::Parser::new(extra)
					}
				}
				mod #ns_name { #rust }
			};
		}
		self.log_last_use(ns, n_line);
		Ok(code.into())
	}

	fn log_last_use(&self, ns: Ns, n_line: usize)
	{	self.last_use.lock().unwrap().insert(ns, (SystemTime::now(), n_line));
	}

	/// This proc-macro crate can be reused by compilers and development tools.
	/// The same instance can be used to scan the same file several times.
	/// If i see that n_line is <= than the last call n_line, and either more than 1 sec passed since last call, or current builder complete, then i will reinitialize self.
	fn reinit_if_needed(&self, ns: Ns, n_line: usize)
	{	let mut want_reinit = false;
		if let Some((at, at_n_line)) = self.last_use.lock().unwrap().get_mut(&ns)
		{	if n_line <= *at_n_line
			{	if let Ok(elapsed) = SystemTime::now().duration_since(*at)
				{	if elapsed.as_millis() > 1000
					{	want_reinit = true;
					}
					else
					{	// maybe requested parser complete
						let map = self.builders.lock().unwrap();
						if let Some(CurBuilder::Complete(_)) = map.get(&ns)
						{	want_reinit = true;
						}
					}
				}
			}
		}
		if want_reinit
		{	self.builders.lock().unwrap().clear();
			self.filenames.lock().unwrap().clear();
			self.last_use.lock().unwrap().clear();
		}
	}

	fn parse_lem_attrs(attrs: &Vec<Attribute>) -> Result<Vec<String>, String>
	{	let mut values = Vec::new();
		for a in attrs
		{	match a.parse_meta()
			{	Ok(Meta::List(list)) =>
				{	if list.path.is_ident("lem")
					{	for a in list.nested.iter()
						{	match a
							{	NestedMeta::Lit(Lit::Str(s)) =>
								{	Alts::split(&s.value(), &mut values)?;
								}
								_ =>
								{	return Err(format!("Cannot parse #[lem(...)]: {}", quote!(#a).to_string()));
								}
							}
						}
					}
				},
				_ => {}
			}
		}
		Ok(values)
	}

	fn parse_lem_opt_attrs(&self, ns: Ns, filename: &Arc<String>, n_line: usize, attrs: &Vec<Attribute>) -> Result<(), String>
	{	for a in attrs
		{	match a.parse_meta()
			{	Ok(Meta::List(list)) =>
				{	if list.path.is_ident("lem_opt")
					{	for a in list.nested
						{	match a
							{	NestedMeta::Meta(Meta::NameValue(list)) =>
								{	self.with_builder
									(	ns, filename, n_line, |builder, grammar|
										{	let value = match list.lit
											{	Lit::Str(s) => s.value(),
												_ =>
												{	return Err("Option value in #[lem_opt(...)] must be string".to_string());
												}
											};
											if list.path.is_ident("extra_argument")
											{	if cfg!(feature = "dump-grammar")
												{	writeln!(grammar, "%extra_argument {{super::super::{}}}", value).map_err(|_| format!("Write to string failed"))?;
												}
												builder.set_extra_argument_type(format!("super::super::{}", value)).map_err(|e| e.to_string())
											}
											else if list.path.is_ident("token_type")
											{	if cfg!(feature = "dump-grammar")
												{	writeln!(grammar, "%token_type {{{}}}", value).map_err(|_| format!("Write to string failed"))?;
												}
												else if cfg!(feature = "dump-lemon-grammar")
												{	writeln!(grammar, "%token_type {{int}}").map_err(|_| format!("Write to string failed"))?;
												}
												builder.set_token_type(value).map_err(|e| e.to_string())
											}
											else if list.path.is_ident("fallback")
											{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
												{	writeln!(grammar, "%fallback {}.", value.trim()).map_err(|_| format!("Write to string failed"))?;
												}
												let v = value.trim_start();
												let pos = v.find(|c: char| c.is_ascii_whitespace()).unwrap_or(v.len());
												let fb_token = &v[.. pos];
												let v = &v[pos ..];
												builder.add_fallback(filename, n_line, fb_token.to_string(), v).map_err(|e| e.to_string())
											}
											else if list.path.is_ident("left")
											{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
												{	writeln!(grammar, "%left {}.", value.trim()).map_err(|_| format!("Write to string failed"))?;
												}
												builder.set_left(filename, n_line, &value).map_err(|e| e.to_string())
											}
											else if list.path.is_ident("right")
											{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
												{	writeln!(grammar, "%right {}.", value.trim()).map_err(|_| format!("Write to string failed"))?;
												}
												builder.set_right(filename, n_line, &value).map_err(|e| e.to_string())
											}
											else if list.path.is_ident("nonassoc")
											{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
												{	writeln!(grammar, "%nonassoc {}.", value.trim()).map_err(|_| format!("Write to string failed"))?;
												}
												builder.set_nonassoc(filename, n_line, &value).map_err(|e| e.to_string())
											}
											else if list.path.is_ident("trace")
											{	if cfg!(feature = "dump-grammar")
												{	writeln!(grammar, "%trace {{{}}}", value).map_err(|_| format!("Write to string failed"))?;
												}
												builder.set_trace_prompt(value).map_err(|e| e.to_string())
											}
											else
											{	Err("Unknown option in #[lem_opt(...)]. Valid options are: token_type=\"Name\", fallback=\"FB A B C\", left=\"A B C\", right=\"A B C\", nonassoc=\"A B C\", trace=\"prompt\"".to_string())
											}
										}
									)?;
								}
								_ =>
								{	return Err("Cannot parse #[lem_opt(...)]".to_string());
								}
							}
						}
					}
				},
				_ => {}
			}
		}
		Ok(())
	}

	// enum: parse_rhs(rhs, n_fields, None, false)
	// struct: parse_rhs(rhs, n_fields, Some(field_names), false)
	// fn: parse_rhs(rhs, n_fields, Some(field_names), true)
	fn parse_rhs(rhs: &str, n_fields: usize, field_names: Option<&Vec<String>>, is_fn: bool) -> Result<(String, Vec<usize>), String>
	{	let mut subst = String::with_capacity(rhs.len()+128);
		let mut aliases = Vec::new();
		let mut s = rhs.trim_start();
		while s.len() != 0
		{	let name_len = s.chars().position(|c| !c.is_ascii_alphanumeric() && c!='_').unwrap_or(s.len());
			if name_len == 0
			{	return Err(format!("Invalid RHS expression: \"{}\"", rhs));
			}
			subst.push_str(&s[.. name_len]);
			s = s[name_len ..].trim_start();
			if s.bytes().next() == Some(b'(')
			{	s = s[1 ..].trim_start();
				let alias_len = s.chars().position(|c| !c.is_ascii_alphanumeric() && c!='_').unwrap_or(s.len());
				let alias = &s[.. alias_len];
				let n = field_names
					.and_then(|v| v.iter().position(|a| a==alias)) // there are field_names and find alias in field_names
					.or_else(|| alias.parse().ok()) // or parse alias
					.filter(|&n| n < n_fields) // accept only 0 .. n_fields
					.ok_or_else
					(	||
						match (field_names, is_fn)
						{	(Some(field_names), true) => format!("No such function argument: {}. Options: {}, or number from 0 to {} exclusive", alias, field_names.join(", "), n_fields),
							(Some(field_names), false) => format!("No such struct field: {}. Options: {}", alias, field_names.join(", ")),
							(None, _) => format!("No such field number in enum variant: {}. Options: 0 .. {} (exclusive)", alias, n_fields),
						}
					)?;
				aliases.push(n);
				subst.push('(');
				if let Some(field_names) = field_names
				{	subst.push_str(&field_names[n]);
				}
				else
				{	subst.push_str("arg_");
					subst.push_str(alias);
				}
				subst.push(')');
				s = s[alias_len ..].trim_start();
				if alias_len==0 || s.bytes().next() != Some(b')')
				{	return Err(format!("Invalid alias in RHS expression: \"{}\"", rhs));
				}
				s = s[1 ..].trim_start();
			}
			subst.push(' ');
		}
		Ok((subst, aliases))
	}

	fn get_location(&self, input: TokenStream) -> Result<(Ns, Arc<String>, usize), String>
	{	let span = input.into_iter().next().unwrap().span();
		let filename = span.source_file();
		let n_line = span.start();
		let is_real_file = filename.is_real();
		let filename = filename.path().to_string_lossy().into_owned();
		let n_line = n_line.line;
		let mut hasher = DefaultHasher::new();
		filename.hash(&mut hasher);
		let hash = hasher.finish();
		let filename = Arc::new(filename);
		let filename = match self.filenames.lock().unwrap().get(&filename)
		{	None => filename,
			Some(filename) => Arc::clone(&filename),
		};
		Ok((Ns{hash, is_real_file}, filename, n_line))
	}

	fn with_builder<F>(&self, ns: Ns, filename: &Arc<String>, n_line: usize, cb: F) -> Result<(), String> where F: FnOnce(LemonMintBuilder, &mut String) -> Result<LemonMintBuilder, String>
	{	let mut map = self.builders.lock().unwrap();
		match map.get_mut(&ns)
		{	None =>
			{	let mut builder = LemonMintBuilder::new();
				let mut grammar = String::new();
				builder = cb(builder, &mut grammar)?;
				map.insert(ns, CurBuilder::Active(builder, grammar));
				Ok(())
			}
			Some(cur_builder) =>
			{	let my_cur_builder = mem::replace(cur_builder, CurBuilder::Complete(usize::MAX));
				match my_cur_builder
				{	CurBuilder::Active(mut builder, mut grammar) =>
					{	builder = cb(builder, &mut grammar)?;
						mem::replace(cur_builder, CurBuilder::Active(builder, grammar));
						Ok(())
					}
					CurBuilder::Complete(complete_n_line) =>
					{	mem::replace(cur_builder, CurBuilder::Complete(complete_n_line));
						Err(format!("#[derive(LemonTree)] must be the last in file. Found at line {}, but additional directive at line {} in file {}", complete_n_line, n_line, filename))
					}
				}
			}
		}
	}

	fn add_type(&self, ns: Ns, filename: &Arc<String>, n_line: usize, name: String, if_not_exists: bool) -> Result<(), String>
	{	self.with_builder
		(	ns, filename, n_line, move |builder, grammar|
			{	let rust_type = format!("super::super::{}", name);
				if cfg!(feature = "dump-grammar")
				{	writeln!(grammar, "%type {} {{{}}}", name, rust_type).map_err(|_| format!("Write to string failed"))?;
				}
				if !if_not_exists || builder.get_type(&name).is_none()
				{	builder.add_type(filename, n_line, name, rust_type).map_err(|e| e.to_string())
				}
				else
				{	Ok(builder)
				}
			}
		)
	}

	fn add_rule(&self, ns: Ns, filename: &Arc<String>, n_line: usize, lhs_name: String, rhs: String, code: String) -> Result<(), String>
	{	self.with_builder
		(	ns, filename, n_line, move |builder, grammar|
			{	if cfg!(feature = "dump-grammar")
				{	writeln!(grammar, "{} ::= {}. {{{}}}", lhs_name, rhs.trim(), code).map_err(|_| format!("Write to string failed"))?;
				}
				else if cfg!(feature = "dump-lemon-grammar")
				{	writeln!(grammar, "{} ::= {}.", Self::lc_first(&lhs_name), Self::rhs_to_lemon(rhs.trim())).map_err(|_| format!("Write to string failed"))?;
				}
				builder.add_rule(filename, n_line, lhs_name, &rhs, code).map_err(|e| e.to_string())
			}
		)
	}

	fn get_lemon_result(&self, ns: Ns, filename: &Arc<String>, n_line: usize, start_symbol_name: String) -> Result<String, String>
	{	let mut map = self.builders.lock().unwrap();
		match map.remove(&ns)
		{	None =>
			{	Err("No parser rules".to_string())
			}
			Some(CurBuilder::Active(mut builder, grammar)) =>
			{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
				{	eprintln!("/* Parser lem_{} from {} */", ns.hash, filename);
				}
				if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
				{	eprintln!("%start_symbol {{{}}}", if cfg!(feature = "dump-lemon-grammar") {Self::lc_first(&start_symbol_name).into()} else {Cow::from(&start_symbol_name)});
				}
				builder = builder.set_start_symbol(&filename, n_line, start_symbol_name).map_err(|e| e.to_string())?;
				if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
				{	eprintln!("{}", grammar);
				}
				let mut rust = Vec::new();
				let lemon = builder.try_into_lemon().map_err(|e| e.to_string())?;
				lemon.gen_rust(&mut rust).map_err(|e| e.to_string())?;
				map.insert
				(	ns,
					if ns.is_real_file
					{	CurBuilder::Complete(n_line)
					}
					else // allow multiple builders in the same file, if this is not a real file (like doc comment)
					{	CurBuilder::Active(LemonMintBuilder::new(), String::new())
					}
				);
				String::from_utf8(rust).map_err(|e| e.to_string())
			}
			Some(CurBuilder::Complete(complete_n_line)) =>
			{	Err(format!("Double #[derive(LemonTree)] in the same file. First at line {}, and then at line {} in file {}", complete_n_line, n_line, filename))
			}
		}
	}

	fn lem_fn_attr(&self, args: TokenStream, item: TokenStream) -> Result<TokenStream, String>
	{	let (ns, filename, n_line) = self.get_location(item.clone())?;
		self.reinit_if_needed(ns, n_line);
		let values = Self::lem_fn_attr_parse(args)?;
		let (fn_name, mut fn_args, fn_return) = Self::lem_fn_attr_parse_fn(item.clone())?;
		let mut has_extra = false;
		for (i, arg) in fn_args.iter().enumerate()
		{	if arg == "extra"
			{	if i != fn_args.len()-1
				{	return Err(format!("Extra argument must be last"));
				}
				has_extra = true;
			}
		}
		if has_extra
		{	fn_args.pop();
		}
		self.add_type(ns, &filename, n_line, fn_return.clone(), true)?;
		for value in values
		{	if !value.trim().is_empty()
			{	let (value, aliases) = Self::parse_rhs(&value, fn_args.len(), Some(&fn_args), true)?;
				let mut action = quote!();
				for i in 0 .. fn_args.len()
				{	if i > 0
					{	action = quote!(#action,);
					}
					if aliases.iter().position(|&a| a==i).is_some()
					{	let arg = Ident::new(&fn_args[i], Span::call_site());
						action = quote!(#action #arg.into());
					}
					else
					{	action = quote!(#action std::default::Default::default());
					}
				}
				if has_extra
				{	if fn_args.len() > 0
					{	action = quote!(#action,);
					}
					action = quote!(#action extra);
				}
				self.add_rule(ns, &filename, n_line, fn_return.clone(), value, quote!(super::super::#fn_name(#action)).to_string())?;
			}
		}
		self.log_last_use(ns, n_line);
		Ok(item)
	}

	fn lem_fn_attr_parse(args: TokenStream) -> Result<Vec<String>, String>
	{	let derive_input = format!("#[lemon({})] struct Tmp;", args);
		let ast: &DeriveInput = &syn::parse_str(&derive_input).map_err(|_| "Cannot parse #[lemon(...)]".to_string())?;
		let attr = ast.attrs.first().ok_or_else(|| "Cannot parse #[lemon(...)]".to_string())?;
		match attr.parse_meta()
		{	Ok(Meta::List(list)) =>
			{	if list.path.is_ident("lemon")
				{	for a in list.nested.iter()
					{	match a
						{	NestedMeta::Lit(Lit::Str(s)) =>
							{	let mut values = Vec::with_capacity(1);
								Alts::split(&s.value(), &mut values)?;
								return Ok(values);
							}
							_ =>
							{	return Err("Cannot parse #[lemon(...)]".to_string());
							}
						}
					}
				}
			},
			_ => {}
		}
		Err("Cannot parse #[lemon(...)]".to_string())
	}

	fn lem_fn_attr_parse_fn(item: TokenStream) -> Result<(Ident, Vec<String>, String), String>
	{	let ast: &ItemFn = &syn::parse(item).map_err(|e| e.to_string())?;
		// fn_name
		let fn_name = ast.sig.ident.clone();
		// fn_return
		let mut fn_return = None;
		let output = &ast.sig.output;
		match output
		{	ReturnType::Default =>
			{	return Err(format!("Function must return an object"));
			}
			ReturnType::Type(_, ty) =>
			{	match &**ty
				{	Type::Path(TypePath {qself: None, path: Path{segments, ..}}) =>
					{	match segments.last()
						{	Some(PathSegment {ident, arguments: PathArguments::None}) =>
							{	fn_return = Some(ident);
							}
							_ => {}
						}
					}
					_ => {}
				}
			}
		};
		let fn_return = fn_return.ok_or_else(|| format!("Couldn't understand function return type. It must be LHS symbol object. Found: {}", quote!(#output)))?;
		// fn_args
		let mut fn_args = Vec::new();
		for arg in &ast.sig.inputs
		{	match arg
			{	FnArg::Receiver(_) =>
				{	return Err(format!("Must be global function"));
				}
				FnArg::Typed(PatType {pat, ..}) =>
				{	match &**pat
					{	Pat::Ident(pat_ident) =>
						{	let mut pat_ident = pat_ident.clone();
							pat_ident.mutability = None;
							fn_args.push(quote!(#pat_ident).to_string());
						}
						_ => {}
					}
				}
			}
		}
		Ok((fn_name, fn_args, fn_return.to_string()))
	}

	fn lc_first(s: &str) -> String
	{	let mut chars = s.chars();
		chars
			.next()
			.map(|first_letter| first_letter.to_lowercase())
			.into_iter()
			.flatten()
			.chain(chars)
			.collect()
	}

	/// Remove aliases, and convert each nonterminal symbol in RHS expression. For me any name that contains lowercase letter is nonterminal, but for lemon first letter must be lowercased.
	fn rhs_to_lemon(rhs: &str) -> String
	{	let mut result = String::new();
		let mut rhs = rhs.trim();
		while !rhs.is_empty()
		{	let pos = rhs.find(|c: char| c.is_ascii_alphanumeric() || c=='_' || c=='(').unwrap_or(rhs.len());
			write!(result, "{}", &rhs[.. pos]).unwrap();
			rhs = &rhs[pos ..];
			if rhs.as_bytes()[0] == b'('
			{	// skip aliases
				let pos = rhs.find(|c: char| c==')').unwrap_or(rhs.len()-1) + 1;
				rhs = &rhs[pos ..];
			}
			else
			{	let pos = rhs.find(|c: char| !c.is_ascii_alphanumeric() && c!='_').unwrap_or(rhs.len());
				let name = &rhs[.. pos];
				if name.find(|c: char| c.is_ascii_lowercase()).is_some()
				{	// is nonterminal
					result.reserve(name.len());
					let mut name = name.chars();
					write!(result, "{}", name.next().unwrap().to_lowercase()).unwrap(); // we know that string is not empty, because there is at least 1 lowercased letter
					for c in name
					{	result.push(c);
					}
				}
				else
				{	write!(result, "{}", name).unwrap();
				}
				rhs = &rhs[pos ..];
			}
		}
		result
	}
}
