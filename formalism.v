Require Import String List.
Import ListNotations.

Fixpoint lookup {A} (ls : list (string * A)) (x : string) : option A :=
  match ls with
  | [] => None
  | (s, a) :: rst => if string_dec s x then Some a else lookup rst x
  end.

Inductive literal : string -> Type :=
  MkLit : forall s, literal s.

Inductive trec : list (string * Type) -> Type :=
| Trec_nil : trec []
| Trec_cons : forall (t : Type) (r : list (string * Type))  (s : string),
    t -> trec r -> trec ((s, t) :: r).

Inductive ty :=
| Unit : ty
| Tag : string -> ty
| Lit : string -> ty
| Pair : ty -> ty -> ty.

Inductive decl : Type :=
| FreeText : string -> decl
| Keywords : string -> list string -> decl
| Trait : string -> list (string * ty) -> decl.

Fixpoint interpTy (env : string -> Type) (t : ty) : Type :=
  match t with
  | Unit => unit
  | Tag tg => env tg
  | Lit l => literal l
  | Pair t1 t2 => (interpTy env t1) * (interpTy env t2)
  end.

Definition interpDecl (env : string -> Type) (d : decl) : Type :=
  match d with
  | FreeText _ => string
  | Keywords _ ls => fold_right (fun x acc => acc + literal x) False ls
  | Trait _ ts => fold_right
                    (fun x acc =>
                       acc + (literal (fst x) * interpTy env (snd x))) False ts
  end%type.

Definition interpDecls (decls : list (string * decl)) : string -> Type :=
  let fix help decls env :=
    match decls with
    | [] => env
    | (t, tp) :: rst =>
      help rst (fun x => if string_dec x t
                         then interpDecl env tp
                         else env x)
    end
  in
  help decls (fun _ => False).

Definition entityData (d : decl) : Type :=
  match d with
  | FreeText _ => string
  | Keywords _ ls => fold_right (fun x acc => acc + literal x) False ls
  | Trait _ ts => fold_right (fun x acc => acc + literal (fst x)) False ts
  end%type.

Definition response (decls : list (string * decl)) :=
  forall e, option match lookup decls e with
                   | Some decl => entityData decl
                   | None => False
                   end.

Open Scope string_scope.
Definition ex : list (string * decl) :=
  [ ("Msg", FreeText "Msg");
    ("Time", Keywords "Time" ["later"; "tomorrow"]);
    ("Intent",
     Trait "Intent" [("Read", Unit); ("Send", (Pair (Tag "Msg") (Tag "Time")))])
  ].

Definition ex_env := interpDecls ex.

Definition ex_resp : response ex.
Proof.
  refine (fun x => if string_dec x "Intent" then  _ else None).
  subst ; simpl.
  refine (Some _).
  right.
  exact (MkLit "Read").
Qed.

Definition parse_resp (decls : list (string * decl)) (resp : response decls)
  : forall s, option (interpDecls decls s).
Proof.
  refine (
      fun s => match lookup decls s with
               | None => None
               | Some d =>
                 match d with
                 | FreeText tg =>
                   match resp tg with
                   | None => None
                   | Some rs => _
                   end
                 | Keywords _ _ => _
                 | Trait _ _ => _
                 end
               end
    ).