-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid
-- name    : GoodReductionJacobian.RelativeGroupLaw.finiteLocallyFree_mono_equivalence_actionGroupoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/c3ff595b-e216-59e8-aaf6-5d4d9dbe7c96
-- title:
--   Finite flat closed subgroup gives finite locally free equivalence relation
-- statement:
--   Let $R$ be a commutative ring, $J$ a scheme with a morphism $f : J \to \operatorname{Spec} R$, and let $L$ be a relative group law on $f$: a group structure, functorial in $T$ via composition, on the sets $\{\varphi : T \to J \mid \varphi \circ f = t\}$ of sections over each $t : T \to \operatorname{Spec} R$, given by operations `mul`, `one`, `inv` satisfying associativity, both unit laws, the left inverse law and naturality of `mul`. Let $\iota : E \to J$ be a closed immersion such that $\iota$ followed by $f$ is finite, flat and locally of finite presentation. Assume that for every $T$ and every $t : T \to \operatorname{Spec} R$ the set of sections over $t$ that factor through $\iota$ contains `L.one t` and is closed under `L.mul t` and `L.inv t`. Then, writing $P = E \times_{\operatorname{Spec} R} J$ for the fibre product of $\iota \circ f$ and $f$: the second projection $P \to J$ is finite, flat and locally of finite presentation; so is the action morphism `L.action ι`, the product of the first projection followed by $\iota$ with the second projection; the pair (projection, action) is jointly monomorphic, i.e. two morphisms $T \to P$ agreeing after both are equal; and for every scheme $T$ the relation on morphisms $T \to J$ given by "there is $\varphi : T \to P$ with $\varphi$ followed by the projection equal to $x$ and $\varphi$ followed by the action equal to $y$" is an equivalence relation.
--
--   This records that the action groupoid $E \times_{\operatorname{Spec} R} J \rightrightarrows J$ attached to a finite flat closed subgroup $E$ of a scheme with a relative group law is a finite locally free, jointly monomorphic equivalence relation, the standard input for forming the quotient $J/E$ by descent. It is used in the construction of the quotient as an abelian scheme property bundle from a finite flat subgroup together with a separately supplied affine-orbit condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.finiteLocallyFree_mono_equivalence_actionGroupoid
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
    [IsFinite (ι ≫ f)] [Flat (ι ≫ f)] [LocallyOfFinitePresentation (ι ≫ f)]
    (hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      ∃ e : T ⟶ E, e ≫ ι = (L.one t).1)
    (hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) →
        ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1)
    (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1) :
    IsFinite (pullback.snd (ι ≫ f) f) ∧ Flat (pullback.snd (ι ≫ f) f) ∧
      LocallyOfFinitePresentation (pullback.snd (ι ≫ f) f) ∧
    IsFinite (L.action ι) ∧ Flat (L.action ι) ∧ LocallyOfFinitePresentation (L.action ι) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ pullback (ι ≫ f) f),
      a ≫ pullback.snd (ι ≫ f) f = b ≫ pullback.snd (ι ≫ f) f → a ≫ L.action ι = b ≫ L.action ι → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ J =>
      ∃ φ : T ⟶ pullback (ι ≫ f) f, φ ≫ pullback.snd (ι ≫ f) f = x ∧ φ ≫ L.action ι = y) := by sorry
