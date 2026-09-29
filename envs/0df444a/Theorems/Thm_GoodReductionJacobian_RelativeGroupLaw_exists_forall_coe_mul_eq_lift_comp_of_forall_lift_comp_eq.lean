-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_coe_mul_eq_lift_comp_of_forall_lift_comp_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_forall_coe_mul_eq_lift_comp_of_forall_lift_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/f1477df3-ceb9-5a30-bcd1-293ab617646d
-- title:
--   Relative group law from morphisms m, e, ι
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism. Suppose given a morphism $m : A \times_f A \to A$ out of the pullback of $f$ along itself with $m$ followed by $f$ equal to the first projection followed by $f$, a morphism $e : \operatorname{Spec} R \to A$ with $e$ followed by $f$ the identity, and a morphism $\iota : A \to A$ with $\iota$ followed by $f$ equal to $f$. For a scheme $T$ with a morphism $t : T \to \operatorname{Spec} R$, write a $T$-point of $A$ over $t$ for a pair consisting of a morphism $x : T \to A$ together with a proof that $x$ followed by $f$ is $t$; any two such points $x,y$ induce $\langle x,y\rangle : T \to A \times_f A$, and one sets $x\cdot y := \langle x,y\rangle$ followed by $m$, $e_T := t$ followed by $e$, and $\iota(x) := x$ followed by $\iota$. Assume that for every such $T$, $t$ and all points $x,y,z$ over $t$ one has $(x\cdot y)\cdot z = x\cdot(y\cdot z)$, $e_T\cdot x = x$, $x\cdot e_T = x$ and $\iota(x)\cdot x = e_T$. Then there exists a term $L$ of the structure `RelativeGroupLaw R f` — consisting of multiplication, unit and inversion operations on the $T$-points of $A$ over $t$ for every $t$, satisfying associativity, both unit laws, left inverses and naturality under base change of the test scheme along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$ — such that the underlying morphisms of $L.mul\,t\,x\,y$, $L.one\,t$ and $L.inv\,t\,x$ are $\langle x,y\rangle$ followed by $m$, $t$ followed by $e$, and $x$ followed by $\iota$ respectively.
--
--   This is the passage from a group-scheme structure given by morphisms $m$, $e$, $\iota$ over $\operatorname{Spec} R$ (with the group axioms stated on points of arbitrary test schemes) to the corresponding group law on the functor of points, in the form used throughout the project. It is invoked in the construction of fake elliptic curves over quaternionic Shimura data, where the multiplication, unit and inverse morphisms are produced by an algebraisation argument and then have to be packaged as a relative group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_coe_mul_eq_lift_comp_of_forall_lift_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_forall_coe_mul_eq_lift_comp_of_forall_lift_comp_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (m : pullback f f ⟶ A) (hm : m ≫ f = pullback.fst f f ≫ f)
    (e : Spec (CommRingCat.of R) ⟶ A) (he : e ≫ f = 𝟙 _)
    (ι : A ⟶ A) (hι : ι ≫ f = f)
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver t f),
      pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
          (by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2, z.2]) ≫ m =
        pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
          (by rw [Category.assoc, hm, pullback.lift_fst_assoc, y.2, x.2]) ≫ m)
    (hone_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      pullback.lift (t ≫ e) x.1 (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1)
    (hmul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      pullback.lift x.1 (t ≫ e) (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1)
    (hinv_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      pullback.lift (x.1 ≫ ι) x.1 (by rw [Category.assoc, hι]) ≫ m = t ≫ e) :
    ∃ L : RelativeGroupLaw R f,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (L.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (L.one t).1 = t ≫ e) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), (L.inv t x).1 = x.1 ≫ ι) := by sorry
