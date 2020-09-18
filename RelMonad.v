
(*
  Context (obj : Type).
  Context (C : obj -> obj -> Type). 
  Context (compose : forall (X Y Z : obj), C X Y -> C Y Z -> C X Z). 
*)
From ITree Require Import 
     ITree
     ITreeFacts
     Basics.Monad.

Class category :=
  {
  obj : Type;
  C : obj -> obj -> Type;
  compose : forall {X Y Z : obj}, C X Y -> C Y Z -> C X Z;
  id : forall {X : obj}, C X X;
  arrow_eq : forall {X Y : obj}, C X Y -> C X Y -> Prop;
  l_id : forall (X Y : obj) (f : C X Y), arrow_eq f (compose id f);
  r_id : forall (X Y : obj) (f : C X Y), arrow_eq f (compose f id);
  assoc : forall (W X Y Z : obj) (f : C W X) (g : C X Y) (h : C Y Z),
      arrow_eq (compose f (compose g h) ) (compose (compose f g) h)
  }.

  Notation "f ∘ g" := (compose f g) (at level 50).
  

Section RelativeMonad.
  Context (C1 C2 : category).
  Context (T J : @obj C1 -> @obj C2).
  Context (Meq : forall (X: @obj C2) (Y : @obj C1), C X (T Y) -> C X (T Y) -> Prop ).
  Notation "f ~ g" := (Meq _ _ f g) (at level 60).

  Class RelMonad :=
    {
    rret : forall {X : obj}, C (J X) (T X);
    rbind : forall {X Y : obj}, C (J X) (T Y) -> C (T X) (T Y);
    rbind_ret : forall (X : obj), rbind (@rret X) ~ id;
    rret_bind : forall (X Y : obj) (f : C (J X) (T Y) ), rret ∘ (rbind f) ~ f;
    rbind_bind : forall (X Y Z : obj) (f : C (J X) (T Y)) (g : C (J Y) (T Z)), 
        (rbind f) ∘ (rbind g) ~ rbind (f ∘ (rbind g));
    }.



End RelativeMonad.

Section TypeCat.
  Program Instance TypeCat : category :=
    {|
    obj := Type;
    C := fun A B => A -> B;
    compose := fun _ _ _ f g x => g (f x);
    id := fun _ x => x;
    arrow_eq := fun _ _ f g => forall x, f x = g x
    |}.


End TypeCat.

Section MonadRelMonad.
  Context (M : Type -> Type).
  Context (EqM : Eq1 M).
  Context (MonadM : Monad M).
  Context (MonadLawsM : MonadLawsE M).

  Program Instance RMM : RelMonad TypeCat TypeCat M (fun x => x) (fun _ _ f g => forall x, EqM _ (f x) (g x))
    :=
    {|
    rret := fun _ x => ret x;
    rbind := fun _ _ k m => bind m k;
    |}.
  Next Obligation .
    cbv. destruct MonadM. destruct MonadLawsM. unfold eq1 in *. auto.
  Qed.
  Next Obligation.
    cbv. destruct MonadLawsM. destruct MonadM. unfold eq1 in *. auto.
  Qed.
  Next Obligation.
    cbv. destruct MonadLawsM. destruct MonadM. unfold eq1 in *. auto.
  Qed.

End MonadRelMonad.

Section VectorRelMonad.
  
