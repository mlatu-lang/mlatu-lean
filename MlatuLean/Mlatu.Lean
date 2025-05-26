import Lean

namespace Mlatu


  inductive Combinator
  | dup : Combinator
  | zap : Combinator
  | swap : Combinator
  | unit : Combinator
  | i : Combinator
  | cat : Combinator
  | atomic : String -> Combinator

  instance : ToString Combinator where
    toString
        | Combinator.dup => "+"
        | Combinator.zap => "-"
        | Combinator.swap => "~"
        | Combinator.unit => ">"
        | Combinator.i => "<"
        | Combinator.cat => ","
        | Combinator.atomic s => s

  mutual
    inductive Term
    | c : Combinator -> Term
    | q : Terms -> Term

    inductive Terms
    | nil
    | concat : Terms -> Term -> Terms
  end

  @[simp]
  def append (x: Terms) : Terms -> Terms
  | Terms.nil => x
  | Terms.concat left a => Terms.concat (append x left) a

  @[simp]
  theorem append_assoc (x y z: Terms) : append x (append y z) = append (append x y) z := by
    cases z with
    | nil =>
        simp only [append]
    | concat ts t =>
        simp only [append, append_assoc]

  @[simp]
  theorem nil_append (x: Terms) : append Terms.nil x = x := by
    cases x with
    | nil =>
      simp only [append]
    | concat ts t =>
      simp only [append, nil_append]

  mutual
    def termToString : Term -> String
        | Term.c combinator => toString combinator
        | Term.q quoted => "(" ++ termsToString quoted ++ ")"

    def termsToString : Terms -> String
        | Terms.nil => ""
        | Terms.concat Terms.nil t => termToString t
        | Terms.concat ts t => termsToString ts ++ " " ++ termToString t
  end

  instance : ToString Term where
    toString := termToString

  instance : ToString Terms where
    toString := termsToString

  open Lean Elab Meta Term Command

  declare_syntax_cat mlatu_combinator
  declare_syntax_cat mlatu_term
  declare_syntax_cat mlatu_terms
  declare_syntax_cat mlatu_eq
  declare_syntax_cat mlatu_atom
  declare_syntax_cat mlatu_var
  declare_syntax_cat mlatu_forall_var

  syntax "+" : mlatu_combinator
  syntax "-" : mlatu_combinator
  syntax "," : mlatu_combinator
  syntax "~" : mlatu_combinator
  syntax "<" : mlatu_combinator
  syntax ">" : mlatu_combinator

  def mkNil: Expr := .const ``Terms.nil []

  def mkConcat (ts: Expr) (t: Expr): Expr := .app (.app (.const ``Terms.concat []) ts) t

  def mkAppend (x: Expr) (y: Expr): Expr := .app (.app (.const ``append []) x) y

  def mkQ (q: Expr): Expr := .app (.const ``Mlatu.Term.q []) q

  def evalVarWith (left: Expr) (var: TSyntax `ident): MetaM Expr := do
    let lctx <- getLCtx
    let name := var.getId
    match LocalContext.findFromUserName? lctx name with
    | some decl => do
      let is_nil <- isDefEq left mkNil
      return if is_nil then (.fvar (LocalDecl.fvarId decl)) else mkAppend left (.fvar (LocalDecl.fvarId decl))
    | none =>
      return mkConcat left (.app (.const ``Mlatu.Term.c []) (.app (.const ``Mlatu.Combinator.atomic []) (.lit (Literal.strVal name.toString))))

   def VarInfo: Type := (Name × BinderInfo × (Array Expr -> MetaM Expr))

  def makeVarName: Nat -> Name
    | n => (Name.mkSimple ("v" ++ toString n))

  def makeDeclInfo (n: Name): VarInfo :=
    (n, BinderInfo.default, fun (_: Array Expr) => return .const ``Mlatu.Terms [])

  def makeDeclInfos (begin: Array VarInfo) (n: Nat): (Array VarInfo) :=
    Prod.snd $ Nat.repeat (fun (n, array) => (n + 1, Array.push array (makeDeclInfo (makeVarName n)))) n (0, begin)

  def concatenateWith (left: Expr): List Expr -> Expr
    | List.nil => left
    | List.cons v vs => concatenateWith (mkConcat left (mkQ v)) vs

  def makeCommon (vars: Array Expr): MetaM Expr :=
    match vars.toList with
    | List.cons left_var List.nil => return left_var
    | List.cons left_var list => return concatenateWith left_var list
    | _ => throwError "unknown array type"

  syntax "(" ident ")" : mlatu_forall_var

  def elabMlatuForallVar : Syntax -> MetaM VarInfo
    | `(mlatu_forall_var| ( $n:ident )) => return makeDeclInfo n.getId
    | _ => throwUnsupportedSyntax

  syntax mlatu_combinator : mlatu_term
  syntax "(" mlatu_terms ")" : mlatu_term
  syntax ident: mlatu_term
  syntax "->": mlatu_term
  syntax "<-": mlatu_term
  syntax "<->": mlatu_term
  syntax ",+": mlatu_term
  syntax "~>": mlatu_term
  syntax "++": mlatu_term
  syntax ">>": mlatu_term

  syntax mlatu_term* : mlatu_terms

  def elabMlatuCombinator: TSyntax `mlatu_combinator -> MetaM Expr
    | `(mlatu_combinator| + ) => return .const ``Mlatu.Combinator.dup []
    | `(mlatu_combinator| - ) => return .const ``Mlatu.Combinator.zap []
    | `(mlatu_combinator| ~ ) => return .const ``Mlatu.Combinator.swap []
    | `(mlatu_combinator| , ) => return .const ``Mlatu.Combinator.cat []
    | `(mlatu_combinator| > ) => return .const ``Mlatu.Combinator.unit []
    | `(mlatu_combinator| < ) => return .const ``Mlatu.Combinator.i []
    | _ => throwUnsupportedSyntax

  mutual
  partial def elabMlatuTerm (left:Expr): Syntax -> MetaM Expr
      | `(mlatu_term| $c:mlatu_combinator) =>
          mkConcat left <$> .app (.const ``Mlatu.Term.c []) <$> elabMlatuCombinator c
      | `(mlatu_term| ( $ts:mlatu_terms ) ) => mkConcat left <$> mkQ <$> elabMlatuTerms mkNil ts
      | `(mlatu_term| $x:ident ) => evalVarWith left x
      | `(mlatu_term| ->) => `(mlatu_terms| - >) >>= elabMlatuTerms left
      | `(mlatu_term| <-) => `(mlatu_terms| < -) >>= elabMlatuTerms left
      | `(mlatu_term| <->) => `(mlatu_terms| < - >) >>= elabMlatuTerms left
      | `(mlatu_term| >>) => `(mlatu_terms| > >) >>= elabMlatuTerms left
      | `(mlatu_term| ,+) => `(mlatu_terms| , +) >>= elabMlatuTerms left
      | `(mlatu_term| ~>) => `(mlatu_terms| ~ >) >>= elabMlatuTerms left
      | `(mlatu_term| ++) => `(mlatu_terms|+ +) >>= elabMlatuTerms left
      | _ => throwUnsupportedSyntax

    partial def elabList (left:Expr) : List Syntax -> MetaM Expr
      | List.cons t ts => do
        let left <- elabMlatuTerm left t
        elabList left ts
      | List.nil => return left

    partial def elabMlatuTerms (left:Expr) : TSyntax `mlatu_terms -> MetaM Expr
      | `(mlatu_terms| $ts:mlatu_term*) => elabList left ts.raw.toList
      | _ => throwUnsupportedSyntax
  end

  syntax mlatu_terms : mlatu_eq
  syntax mlatu_terms "=" mlatu_terms : mlatu_eq
    def elabMlatuEq (input: (Array Expr)) (n: Nat) (syn: TSyntax `mlatu_eq): MetaM Expr :=
      withLocalDecls (makeDeclInfos #[makeDeclInfo `left] n) (fun vars => do
        let common <-  makeCommon vars
        let body <- match syn with
        | `(mlatu_eq| $left:mlatu_terms = $right:mlatu_terms) => do
          let left <- elabMlatuTerms (concatenateWith common input.toList) left
          let right <- elabMlatuTerms common right
          mkAppM ``Eq #[left, right]
        | `(mlatu_eq| $only:mlatu_terms) => elabMlatuTerms common only
        | _ => throwUnsupportedSyntax
        mkForallFVars vars body)

    def elabMlatuForallEq (n: Nat) (syn: TSyntax `mlatu_eq) (vars: Array VarInfo) : MetaM Expr :=
      withLocalDecls vars (fun prefix_vars => elabMlatuEq prefix_vars n syn >>= mkForallFVars prefix_vars)

    declare_syntax_cat mlatu_forall
    syntax mlatu_eq : mlatu_forall
    syntax num ":" mlatu_eq : mlatu_forall
    syntax "$" num mlatu_eq : mlatu_forall
    syntax mlatu_forall_var* "." mlatu_eq : mlatu_forall

    def elabMlatuForall : TSyntax `mlatu_forall -> MetaM Expr
      | `(mlatu_forall| $eq: mlatu_eq) => elabMlatuEq #[] 0 eq
      | `(mlatu_forall| $n:num : $eq:mlatu_eq) => elabMlatuEq #[] n.getNat eq
      | `(mlatu_forall| $ $n:num $eq:mlatu_eq) => elabMlatuForallEq 0 eq (makeDeclInfos #[] n.getNat)
      | `(mlatu_forall| $vs:mlatu_forall_var* . $eq:mlatu_eq) => vs.raw.mapM elabMlatuForallVar >>= elabMlatuForallEq 0 eq
      | _ => throwUnsupportedSyntax

  elab "<<<" f:mlatu_forall ">>>" :  term => elabMlatuForall f

  declare_syntax_cat mlatu_define
  syntax "def" ident "/" num "=" mlatu_terms "." : mlatu_define

  def elabMlatuDefine: CommandElab
    | `(mlatu_define| def $x:ident / $n:num = $right:mlatu_terms . ) => do
      let eq: TSyntax `mlatu_eq <- `(mlatu_eq| $x:ident = $right:mlatu_terms)
      let f: TSyntax `mlatu_forall <- `(mlatu_forall| $n:num : $eq)
      let command <- `(@[simp] axiom x : <<< $f >>>)
      elabCommand command
    | _ => throwUnsupportedSyntax

  declare_syntax_cat mlatu_assert
  syntax "assert" mlatu_forall_var* ident "=" mlatu_terms "." : mlatu_assert
  syntax "assert" ident "/" num "=" mlatu_terms "." : mlatu_assert
  syntax "assert" "/" num mlatu_terms "=" mlatu_terms "." : mlatu_assert

  def elabMlatuAssert: CommandElab
    | `(mlatu_assert| assert $fvs:mlatu_forall_var* $x:ident = $right:mlatu_terms . ) => do
      let eq: TSyntax `mlatu_eq <- `(mlatu_eq| $x:ident = $right:mlatu_terms)
      let f: TSyntax `mlatu_forall <- `(mlatu_forall| $fvs:mlatu_forall_var* . $eq)
      let command <- `(example : <<< $f >>> := by intros; simp )
      elabCommand command
    | `(mlatu_assert| assert $x:ident / $n:num = $right:mlatu_terms . ) => do
      let eq: TSyntax `mlatu_eq <- `(mlatu_eq| $x:ident = $right:mlatu_terms)
      let f: TSyntax `mlatu_forall <- `(mlatu_forall| $n:num : $eq)
      let command <- `(example : <<< $f >>> := by intros; simp )
      elabCommand command
    | `(mlatu_assert| assert / $n:num $left:mlatu_terms = $right:mlatu_terms . ) => do
      let eq: TSyntax `mlatu_eq <- `(mlatu_eq| $left:mlatu_terms = $right:mlatu_terms)
      let f: TSyntax `mlatu_forall <- `(mlatu_forall| $n:num : $eq)
      let command <- `(example : <<< $f >>> := by intros; simp )
      elabCommand command
    | _ => throwUnsupportedSyntax

  def get_arity: TSyntax `mlatu_combinator -> MetaM (TSyntax `num)
      | `(mlatu_combinator| +)  =>  `(num| 1)
      | `(mlatu_combinator| -)  =>  `(num| 1)
      | `(mlatu_combinator| <)  =>  `(num| 1)
      | `(mlatu_combinator| >) =>  `(num| 1)
      | `(mlatu_combinator| ~) =>  `(num| 2)
      | `(mlatu_combinator| ,) =>  `(num| 2)
      | _ => throwUnsupportedSyntax

  elab d:mlatu_define: command => elabMlatuDefine d

  elab a:mlatu_assert: command => elabMlatuAssert a

end Mlatu

@[simp]
axiom dup_base: <<< (a). + = (a) (a) >>>

@[simp]
axiom zap_base: <<< (a). - = >>>

@[simp]
axiom unit_base: <<< (a). > = ((a)) >>>

@[simp]
axiom swap_base: <<< (b) (a). ~ = (a) (b) >>>

@[simp]
axiom cat_base: <<< (b) (a). , = (b a) >>>

@[simp]
axiom i_base: <<< (a). < = a >>>
