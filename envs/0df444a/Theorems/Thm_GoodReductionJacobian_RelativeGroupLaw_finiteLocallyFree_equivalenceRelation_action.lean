-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action
-- name    : GoodReductionJacobian.RelativeGroupLaw.finiteLocallyFree_equivalenceRelation_action
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/708484eb-94d8-53e7-9fc9-e606e4202db0
-- title:
--   Finite locally free equivalence relation from a finite flat subgroup
-- statement:
--   Let $R$ be a commutative ring, $f : J \to \operatorname{Spec} R$ a scheme over $R$, and $L$ a relative group law on $f$: a group structure (operations `mul`, `one`, `inv` with associativity, both unit laws, left inverse, and naturality of `mul` under base change) on the sets $\{\varphi : T \to J \mid \varphi \circ f = t\}$ for every $R$-scheme $t : T \to \operatorname{Spec} R$. Let $\iota : E \to J$ be a closed immersion such that $\iota$ followed by $f$ is finite, flat and locally of finite presentation, and suppose that for every $t : T \to \operatorname{Spec} R$ the unit $L.\mathrm{one}\,t$ factors through $\iota$, and that products and inverses of points factoring through $\iota$ again factor through $\iota$. Assume finally that every finite set of points of $J$ lies in some affine open. Write $s = \mathrm{pr}_2 : E \times_{\operatorname{Spec} R} J \to J$ and let $a = L.\mathrm{action}\,\iota$ be the product of $\mathrm{pr}_1$ followed by $\iota$ with $\mathrm{pr}_2$, formed in the group on points of the pullback over $R$. The conclusion is the conjunction: $s$ is finite, flat and locally of finite presentation; $a$ is finite, flat and locally of finite presentation; any two maps $T \to E \times_{\operatorname{Spec} R} J$ agreeing after composition with both $s$ and $a$ are equal; for every $T$ the relation on $T \to J$ given by $x \sim y$ iff some $\varphi$ satisfies $\varphi$ followed by $s$ equals $x$ and $\varphi$ followed by $a$ equals $y$ is an equivalence relation; and for every point $x$ of $J$ there is an affine open $U$ containing $a(r)$ for all points $r$ with $s(r) = x$.
--
--   This verifies that the action groupoid of a finite flat closed subgroup scheme $E \subseteq J$ is a finite locally free equivalence relation on $J$ whose orbits lie in affine opens, i.e. exactly the input required by the descent construction of the quotient $J/E$. It is used in the construction of quotients of Jacobians (and abelian schemes) by finite flat subgroup schemes, in [`GoodReductionJacobian.RelativeGroupLaw.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.finiteLocallyFree_equivalenceRelation_action
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
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)
    (hAF : ∀ S : Finset J, ∃ U : J.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    IsFinite (pullback.snd (ι ≫ f) f) ∧ Flat (pullback.snd (ι ≫ f) f) ∧
      LocallyOfFinitePresentation (pullback.snd (ι ≫ f) f) ∧
    IsFinite (L.action ι) ∧ Flat (L.action ι) ∧ LocallyOfFinitePresentation (L.action ι) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ pullback (ι ≫ f) f),
      a ≫ pullback.snd (ι ≫ f) f = b ≫ pullback.snd (ι ≫ f) f → a ≫ L.action ι = b ≫ L.action ι → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ J =>
      ∃ φ : T ⟶ pullback (ι ≫ f) f, φ ≫ pullback.snd (ι ≫ f) f = x ∧ φ ≫ L.action ι = y) ∧
    (∀ x : J, ∃ U : J.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (ι ≫ f) f), (pullback.snd (ι ≫ f) f) r = x → (L.action ι) r ∈ U) := by sorry
