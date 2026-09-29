-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/d40db5d4-18ba-5aba-942b-861f815488c7
-- title:
--   Finite subgroup of k-points as reduced finite closed subscheme
-- statement:
--   Let $k$ be an algebraically closed field, let $Y$ be a scheme and let $h : Y \to \operatorname{Spec} k$ be separated and locally of finite type. Let $L$ be a relative group law on $h$, i.e. a family of group structures, natural in the base change, on the sets $\{x : T \to Y \mid x \text{ followed by } h = t\}$ of $T$-points for every $t : T \to \operatorname{Spec} k$, with operations `L.mul`, `L.one`, `L.inv`. Let $Z$ be a finite set of $k$-points, that is, of morphisms $\operatorname{Spec} k \to Y$ over the identity of $\operatorname{Spec} k$, containing `L.one`, closed under `L.mul` and closed under `L.inv`. The conclusion provides a scheme $B$, a morphism $g : B \to \operatorname{Spec} k$, a relative group law $L_B$ on $g$ and a morphism $i : B \to Y$ with $i$ followed by $h$ equal to $g$, such that $B$ is reduced, $g$ is finite and $i$ is a closed immersion; composition with $i$ carries $L_B$-multiplication of $T$-points to $L$-multiplication of $T$-points, for every $t : T \to \operatorname{Spec} k$; and there is a bijection from the $k$-points of $g$ onto $Z$ sending $y$ to the $k$-point $y$ followed by $i$. The last clause is thus an explicit bijection rather than a membership criterion.
--
--   This is the statement that a finite subgroup of the group of $k$-points of a separated group scheme locally of finite type over an algebraically closed field $k$ is realised as the group of $k$-points of a reduced finite closed subgroup scheme, in arbitrary characteristic. It is used in the construction of fake elliptic curves with extra level structure and of their quotients by finite subgroups in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated h] [LocallyOfFiniteType h]
    (L : RelativeGroupLaw k h)
    (Z : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h)) (hZ : Z.Finite)
    (hone : L.one _ ∈ Z)
    (hmul : ∀ x ∈ Z, ∀ y ∈ Z, L.mul _ x y ∈ Z)
    (hinv : ∀ x ∈ Z, L.inv _ x ∈ Z) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of k)) (LB : RelativeGroupLaw k g) (i : SchemeHomOver g h),
      IsReduced B ∧ IsFinite g ∧ IsClosedImmersion i.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) i =
          L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i)) ∧
      (∃ eB : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g ≃ ↥Z,
        ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
          ((eB y : ↥Z) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) = NeronModelInfra.schemeHomOverComp y i) := by sorry
