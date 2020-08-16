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
use syn::{self, DeriveInput, DataEnum, Data, Attribute, Meta, NestedMeta, Lit, Ident, ItemFn, ReturnType, Type, TypePath, Path, PathSegment, PathArguments, FnArg, PatType, Pat, GenericArgument, export::Span};
use crate::proc_macro::TokenStream;
use quote::quote;
use once_cell::sync::OnceCell;
use lemon_mint::LemonMintBuilder;
use std::borrow::Cow;
use std::fmt::Write;

static DERIVE: OnceCell<Derive> = OnceCell::new();

#[proc_macro_derive(LemonTree, attributes(lem, lem_opt))]
pub fn derive_lemon_tree(input: TokenStream) -> TokenStream
{	match DERIVE.get_or_init(|| Default::default()).derive(input, true)
	{	Ok(ts) => ts,
		Err(error) => panic!(error),
	}
}

#[proc_macro_derive(LemonTreeNode, attributes(lem))]
pub fn derive_lemon_tree_node(input: TokenStream) -> TokenStream
{	match DERIVE.get_or_init(|| Default::default()).derive(input, false)
	{	Ok(ts) => ts,
		Err(error) => panic!(error),
	}
}

#[proc_macro_attribute]
pub fn lem_fn(attr: TokenStream, item: TokenStream) -> TokenStream
{	match DERIVE.get_or_init(|| Default::default()).lem_fn_attr(attr, item)
	{	Ok(item) => item,
		Err(error) => panic!(error),
	}
}

struct AddType
{	filename: Arc<String>,
	n_line: usize,
	name: String,
}

struct AddRule
{	filename: Arc<String>,
	n_line: usize,
	lhs_name: String,
	rhs: String,
	code: String,
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

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum LemOptName
{	ExtraArgument,
	TokenType,
	Fallback,
	Left,
	Right,
	Nonassoc,
	Trace,
}

struct LemOptValue
{	filename: Arc<String>,
	n_line: usize,
	value: String,
}

struct TailRecursion<'a>
{	item_variant: &'a Ident,
	items_variant: &'a Ident,
	item_type: &'a Ident,
	is_head_recursion: bool,
}

struct ParserDefs
{	add_types: Vec<AddType>,
	add_rules: Vec<AddRule>,
	lem_opts: Vec<(LemOptName, LemOptValue)>,
	complete_line: usize,
}

#[derive(Default)]
struct Derive
{	parser_defs: Mutex<HashMap<u64, ParserDefs>>,
	filenames: Mutex<HashSet<Arc<String>>>,
	last_use: Mutex<HashMap<u64, (SystemTime, usize)>>,
}

impl Derive
{	pub fn derive(&self, input: TokenStream, is_start_symbol: bool) -> Result<TokenStream, String>
	{	let (ns, filename, n_line) = self.get_location(input.clone())?;
		self.reinit_if_needed(ns, n_line);
		let ast: &DeriveInput = &syn::parse(input).unwrap();
		let name = &ast.ident;
		let mut tail_recursion = None;
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
				// is this enum a tail recursion?
				tail_recursion = Self::is_tail_recursion(name, &data_enum);
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
			let ns_name = Ident::new(&format!("lem_{}", ns), Span::call_site());
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
		if let Some(TailRecursion {item_variant, items_variant, item_type, is_head_recursion}) = tail_recursion
		{	let iter_type_name = Ident::new(&format!("{}Iter", name), Span::call_site());
			let item_names = if !is_head_recursion {quote!(items, item)} else {quote!(item, items)};
			let item_names_opt = if !is_head_recursion {quote!(items, _item)} else {quote!(_item, items)};
			code = quote!
			{	#code

				impl #name
				{	fn len(&self) -> usize
					{	match self
						{	#name::#item_variant(_item) => 1,
							#name::#items_variant(#item_names_opt) => 1 + items.len(),
						}
					}
				}
				impl IntoIterator for #name
				{	type Item = #item_type;
					type IntoIter = #iter_type_name;

					fn into_iter(self) -> Self::IntoIter
					{	#iter_type_name {len: self.len(), item: Some(self)}
					}
				}
				pub struct #iter_type_name
				{	item: Option<#name>,
					len: usize,
				}
				impl Iterator for #iter_type_name
				{	type Item = #item_type;

					fn size_hint(&self) -> (usize, Option<usize>)
					{	(self.len, Some(self.len))
					}

					fn next(&mut self) -> Option<Self::Item>
					{	match self.item.take()
						{	None => None,
							Some(#name::#item_variant(item)) =>
							{	self.item = None;
								self.len -= 1;
								Some(item)
							},
							Some(#name::#items_variant(#item_names)) =>
							{	self.item = Some(*items);
								self.len -= 1;
								Some(item)
							}
						}
					}
				}
				impl Into<Vec<#item_type>> for #name
				{	fn into(self) -> Vec<#item_type>
					{	self.into_iter().collect()
					}
				}
			};
		}
		self.log_last_use(ns, n_line);
		Ok(code.into())
	}

	fn log_last_use(&self, ns: u64, n_line: usize)
	{	self.last_use.lock().unwrap().insert(ns, (SystemTime::now(), n_line));
	}

	/// This proc-macro crate can be reused by compilers and development tools.
	/// The same instance can be used to scan the same file several times.
	/// If i see that n_line is <= than the last call n_line, and more than 1 sec passed since last call, i will reinitialize self.
	fn reinit_if_needed(&self, ns: u64, n_line: usize)
	{	let mut want_reinit = false;
		if let Some((at, at_n_line)) = self.last_use.lock().unwrap().get_mut(&ns)
		{	if n_line <= *at_n_line
			{	if let Ok(elapsed) = SystemTime::now().duration_since(*at)
				{	if elapsed.as_millis() > 1000
					{	want_reinit = true;
					}
				}
			}
		}
		if want_reinit
		{	self.parser_defs.lock().unwrap().clear();
			self.filenames.lock().unwrap().clear();
			self.last_use.lock().unwrap().clear();
		}
	}

	fn is_tail_recursion<'a>(enum_name: &'a Ident, data_enum: &'a DataEnum) -> Option<TailRecursion<'a>>
	{	let mut has_one = false; // has variant Item(ItemType)
		let mut has_two = false; // has variant Items(Box<EnumName>, ItemType)
		let mut item_type = None; // ItemType
		let mut item_variant = None; // Item for EnumName::Item
		let mut items_variant = None; // Items for EnumName::Items
		let mut is_head_recursion = false; // true if Items(ItemType, Box<EnumName>), false if Items(Box<EnumName>, ItemType)
		if data_enum.variants.len() != 2
		{	return None;
		}
		for variant in &data_enum.variants
		{	if variant.fields.len()==0 || variant.fields.len()>2
			{	return None;
			}
			let mut item_n = usize::MAX;
			let mut items_n = usize::MAX;
			for (i, field) in variant.fields.iter().enumerate()
			{	match field.ty
				{	Type::Path(TypePath {qself: None, path: Path {leading_colon: None, ref segments}}) =>
					{	if segments.len() != 1
						{	return None;
						}
						let seg = &segments[0];
						match seg.arguments
						{	PathArguments::None =>
							{	// like Name
								if let Some(cur) = item_type
								{	if cur != &seg.ident
									{	return None;
									}
								}
								item_type = Some(&seg.ident);
								item_n = i;
							}
							PathArguments::AngleBracketed(ref args) =>
							{	// like Box<Name>
								if seg.ident=="Box" && args.args.len()==1
								{	match args.args[0]
									{	GenericArgument::Type(Type::Path(TypePath {qself: None, path: Path {leading_colon: None, ref segments}})) =>
										{	if segments.len() != 1
											{	return None;
											}
											let seg = &segments[0];
											match seg.arguments
											{	PathArguments::None =>
												{	if seg.ident != *enum_name
													{	return None;
													}
													items_n = i;
												}
												_ => return None
											}
										}
										_ => return None
									}
								}
							}
							_ => return None
						}
					}
					_ => return None
				}
			}
			if item_n == usize::MAX
			{	return None;
			}
			if variant.fields.len() == 1
			{	if has_one
				{	return None;
				}
				has_one = true;
				item_variant = Some(&variant.ident);
			}
			else
			{	if items_n == usize::MAX
				{	return None;
				}
				if has_two
				{	return None;
				}
				has_two = true;
				is_head_recursion = item_n == 0;
				items_variant = Some(&variant.ident);
			}
		}
		if !has_one || !has_two
		{	return None;
		}
		Some
		(	TailRecursion
			{	item_variant: item_variant.unwrap(),
				items_variant: items_variant.unwrap(),
				item_type: item_type.unwrap(),
				is_head_recursion
			}
		)
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

	fn parse_lem_opt_attrs(&self, ns: u64, filename: &Arc<String>, n_line: usize, attrs: &Vec<Attribute>) -> Result<(), String>
	{	for a in attrs
		{	match a.parse_meta()
			{	Ok(Meta::List(list)) =>
				{	if list.path.is_ident("lem_opt")
					{	for a in list.nested
						{	match a
							{	NestedMeta::Meta(Meta::NameValue(list)) =>
								{	let value = match list.lit
									{	Lit::Str(s) => s.value(),
										_ =>
										{	return Err("Option value in #[lem_opt(...)] must be string".to_string());
										}
									};
									if list.path.is_ident("extra_argument")
									{	self.add_lem_opt(ns, filename, n_line, LemOptName::ExtraArgument, value)?;
									}
									else if list.path.is_ident("token_type")
									{	self.add_lem_opt(ns, filename, n_line, LemOptName::TokenType, value)?;
									}
									else if list.path.is_ident("fallback")
									{	self.add_lem_opt(ns, filename, n_line, LemOptName::Fallback, value)?;
									}
									else if list.path.is_ident("left")
									{	self.add_lem_opt(ns, filename, n_line, LemOptName::Left, value)?;
									}
									else if list.path.is_ident("right")
									{	self.add_lem_opt(ns, filename, n_line, LemOptName::Right, value)?;
									}
									else if list.path.is_ident("nonassoc")
									{	self.add_lem_opt(ns, filename, n_line, LemOptName::Nonassoc, value)?;
									}
									else if list.path.is_ident("trace")
									{	self.add_lem_opt(ns, filename, n_line, LemOptName::Trace, value)?;
									}
									else
									{	return Err("Unknown option in #[lem_opt(...)]. Valid options are: token_type=\"Name\", fallback=\"FB A B C\", left=\"A B C\", right=\"A B C\", nonassoc=\"A B C\", trace=\"prompt\"".to_string());
									}
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

	fn get_location(&self, input: TokenStream) -> Result<(u64, Arc<String>, usize), String>
	{	let span = input.into_iter().next().unwrap().span();
		let filename = span.source_file();
		let n_line = span.start();
		if !filename.is_real()
		{	return Err("Unknown filename".to_string());
		}
		let filename = filename.path().to_string_lossy().into_owned();
		let n_line = n_line.line;
		let mut hasher = DefaultHasher::new();
		filename.hash(&mut hasher);
		let ns = hasher.finish();
		let filename = Arc::new(filename);
		let filename = match self.filenames.lock().unwrap().get(&filename)
		{	None => filename,
			Some(filename) => Arc::clone(&filename),
		};
		Ok((ns, filename, n_line))
	}

	fn add_type(&self, ns: u64, filename: &Arc<String>, n_line: usize, name: String, if_not_exists: bool) -> Result<(), String>
	{	let mut map = self.parser_defs.lock().unwrap();
		let add = AddType {filename: Arc::clone(filename), n_line, name};
		match map.get_mut(&ns)
		{	None =>
			{	let mut add_types = Vec::with_capacity(64);
				let add_rules = Vec::with_capacity(64);
				let lem_opts = Vec::new();
				add_types.push(add);
				map.insert(ns, ParserDefs {add_types, add_rules, lem_opts, complete_line: usize::MAX});
			}
			Some(parser_defs) =>
			{	if parser_defs.complete_line != usize::MAX
				{	return Err(format!("#[derive(LemonTree)] must be the last in file. Found at line {}, but additional directive at line {} in file {}", parser_defs.complete_line, n_line, filename));
				}
				if !if_not_exists || parser_defs.add_types.iter().position(|d| d.name==add.name).is_none()
				{	parser_defs.add_types.push(add);
				}
			}
		}
		Ok(())
	}

	fn add_rule(&self, ns: u64, filename: &Arc<String>, n_line: usize, lhs_name: String, rhs: String, code: String) -> Result<(), String>
	{	let mut map = self.parser_defs.lock().unwrap();
		if let Some(parser_defs) = map.get_mut(&ns)
		{	if parser_defs.complete_line != usize::MAX
			{	return Err(format!("#[derive(LemonTree)] must be the last in file. Found at line {}, but additional directive at line {} in file {}", parser_defs.complete_line, n_line, filename));
			}
			parser_defs.add_rules.push(AddRule {filename: Arc::clone(filename), n_line, lhs_name, rhs, code});
		}
		Ok(())
	}

	fn add_lem_opt(&self, ns: u64, filename: &Arc<String>, n_line: usize, name: LemOptName, value: String) -> Result<(), String>
	{	let mut map = self.parser_defs.lock().unwrap();
		if let Some(parser_defs) = map.get_mut(&ns)
		{	if parser_defs.complete_line != usize::MAX
			{	return Err(format!("#[derive(LemonTree)] must be the last in file. Found at line {}, but additional directive at line {} in file {}", parser_defs.complete_line, n_line, filename));
			}
			parser_defs.lem_opts.push((name, LemOptValue {filename: Arc::clone(filename), n_line, value}));
		}
		Ok(())
	}

	fn get_lemon_result(&self, ns: u64, filename: &Arc<String>, n_line: usize, start_symbol_name: String) -> Result<String, String>
	{	let mut map = self.parser_defs.lock().unwrap();
		if let Some(parser_defs) = map.get_mut(&ns)
		{	if parser_defs.complete_line != usize::MAX
			{	return Err(format!("Double #[derive(LemonTree)] in the same file. First at line {}, and then at line {} in file {}", parser_defs.complete_line, n_line, filename));
			}
			let add_types = mem::replace(&mut parser_defs.add_types, Vec::new());
			let add_rules = mem::replace(&mut parser_defs.add_rules, Vec::new());
			let lem_opts = mem::replace(&mut parser_defs.lem_opts, Vec::new());
			if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
			{	eprintln!("/* Parser lem_{} from {} */", ns, filename);
			}
			let mut builder = LemonMintBuilder::new();
			if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
			{	eprintln!("%start_symbol {{{}}}", if cfg!(feature = "dump-lemon-grammar") {Self::lc_first(&start_symbol_name).into()} else {Cow::from(&start_symbol_name)});
			}
			builder = builder.set_start_symbol(&filename, n_line, start_symbol_name).map_err(|e| e.to_string())?;
			for add in add_types
			{	let rust_type = format!("super::super::{}", add.name);
				if cfg!(feature = "dump-grammar")
				{	eprintln!("%type {} {{{}}}", add.name, rust_type);
				}
				builder = builder.add_type(&add.filename, add.n_line, add.name, rust_type).map_err(|e| e.to_string())?;
			}
			for (name, value) in lem_opts
			{	match name
				{	LemOptName::ExtraArgument =>
					{	if cfg!(feature = "dump-grammar")
						{	eprintln!("%extra_argument {{super::super::{}}}", value.value);
						}
						builder = builder.set_extra_argument_type(format!("super::super::{}", value.value)).map_err(|e| e.to_string())?;
					}
					LemOptName::TokenType =>
					{	if cfg!(feature = "dump-grammar")
						{	eprintln!("%token_type {{{}}}", value.value);
						}
						else if cfg!(feature = "dump-lemon-grammar")
						{	eprintln!("%token_type {{int}}");
						}
						builder = builder.set_token_type(value.value).map_err(|e| e.to_string())?;
					}
					LemOptName::Fallback =>
					{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
						{	eprintln!("%fallback {}.", value.value.trim());
						}
						let v = value.value.trim_start();
						let pos = v.find(|c: char| c.is_ascii_whitespace()).unwrap_or(v.len());
						let fb_token = &v[.. pos];
						let v = &v[pos ..];
						builder = builder.add_fallback(&value.filename, value.n_line, fb_token.to_string(), v).map_err(|e| e.to_string())?;
					}
					LemOptName::Left =>
					{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
						{	eprintln!("%left {}.", value.value.trim());
						}
						builder = builder.set_left(&value.filename, value.n_line, &value.value).map_err(|e| e.to_string())?;
					}
					LemOptName::Right =>
					{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
						{	eprintln!("%right {}.", value.value.trim());
						}
						builder = builder.set_right(&value.filename, value.n_line, &value.value).map_err(|e| e.to_string())?;
					}
					LemOptName::Nonassoc =>
					{	if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
						{	eprintln!("%nonassoc {}.", value.value.trim());
						}
						builder = builder.set_nonassoc(&value.filename, value.n_line, &value.value).map_err(|e| e.to_string())?;
					}
					LemOptName::Trace =>
					{	if cfg!(feature = "dump-grammar")
						{	eprintln!("%trace {{{}}}", value.value);
						}
						builder = builder.set_trace_prompt(value.value).map_err(|e| e.to_string())?;
					}
				}
			}
			for add in add_rules
			{	if cfg!(feature = "dump-grammar")
				{	eprintln!("{} ::= {}. {{{}}}", add.lhs_name, add.rhs.trim(), add.code);
				}
				else if cfg!(feature = "dump-lemon-grammar")
				{	eprintln!("{} ::= {}.", Self::lc_first(&add.lhs_name), Self::rhs_to_lemon(add.rhs.trim()));
				}
				builder = builder.add_rule(&add.filename, add.n_line, add.lhs_name, &add.rhs, add.code).map_err(|e| e.to_string())?;
			}
			if cfg!(feature = "dump-grammar") || cfg!(feature = "dump-lemon-grammar")
			{	eprintln!();
			}
			let mut rust = Vec::new();
			let lemon = builder.try_into_lemon().map_err(|e| e.to_string())?;
			lemon.gen_rust(&mut rust).map_err(|e| e.to_string())?;
			parser_defs.complete_line = n_line;
			return String::from_utf8(rust).map_err(|e| e.to_string());
		};
		Err("No parser rules".to_string())
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
