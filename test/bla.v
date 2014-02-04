Require Import mtac.

Require Import ssreflect.

Inductive CtxType : Type :=
  | CtxParam : Type -> CtxType
  | CtxBase : Type -> CtxType
  | CtxTele : forall {A : Type},
           (A -> CtxType) -> CtxType.

Notation "'<|' '|>' A" := (CtxBase A)
  (at level 100, A at next level).
Notation "'<|' x .. y '|>' A" := (CtxTele (fun x=> .. (CtxTele (fun y=>CtxBase A)).. ))
  (at level 100, x binder, y binder, A at next level).
Notation "'<|' 'phi' x .. y '|>' A" := (CtxTele (fun x=> .. (CtxTele (fun y=>CtxParam A)).. ))
  (at level 100, x binder, y binder, A at next level).
Notation "'<|' 'phi' '|>' A" := (CtxParam A)
  (at level 100, A at next level).




Definition ex1 := <| (x : nat) (y : nat) |> x > y.

Inductive hasCT : forall {A}, A -> CtxType -> Type :=
  | hasParam : forall {A : Type} (x : A), hasCT x (CtxParam A)
  | hasBase : forall {A : Type} (x : A), hasCT x (CtxBase A)
  | hasTele : forall {A : Type} {P} (t : forall x : A, P x) f, 
                (forall (x : A), hasCT (t x) (f x)) ->
                hasCT t (CtxTele f).

Definition bla : hasCT (fun x y: nat=>x + y) (<| phi x y : nat|> nat).
Proof.
  apply: hasTele.
  move=>x.
  apply: hasTele.
  move=>y.
  apply: hasParam.
Qed.

Definition bla' : hasCT (fun x y: nat=>x + y) (<| phi |> nat -> nat -> nat).
Proof.
  apply: hasParam.
Qed.

Definition bla'' : hasCT (fun x y: nat=>x + y) (<| |> nat -> nat -> nat).
Proof.
  apply: hasBase.
Qed.





