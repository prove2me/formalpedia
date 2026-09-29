-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_comp_eq_one_iff
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_comp_eq_one_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/ae049c53-63b8-5153-94c3-8b29e3b8a9fa
-- title:
--   Common kernel of two morphisms to relative group laws is closed
-- statement:
--   Let $k$ be a field and let $D, D_1, D_2$ be schemes, equipped with structure morphisms $d \colon D \to \operatorname{Spec} k$, $d_1 \colon D_1 \to \operatorname{Spec} k$, $d_2 \colon D_2 \to \operatorname{Spec} k$. Suppose given relative group laws $L_1$ on $d_1$ and $L_2$ on $d_2$: for each $k$-scheme $t \colon T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to D_i \mid \varphi \circ d_i = t\}$ of $T$-points of $D_i$ over $k$, satisfying associativity, the two unit laws and left inversion, together with naturality under base change along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Suppose also given $k$-morphisms $\nu_1 \colon D \to D_1$ and $\nu_2 \colon D \to D_2$, that is, morphisms with $\nu_i \circ d_i = d$. The assertion is that there exist a scheme $K$ and a closed immersion $j \colon K \to D$ such that for every scheme $T$, every $t \colon T \to \operatorname{Spec} k$ and every $a \colon T \to D$ with $a \circ d = t$, the $T$-point $\nu_1 \circ a$ equals the unit of $L_1$ at $t$ and $\nu_2 \circ a$ equals the unit of $L_2$ at $t$ if and only if $a$ factors as $b$ followed by $j$ for some $b \colon T \to K$. No uniqueness of $b$, and no compatibility of $b$ with the structure morphisms, is asserted.
--
--   This realises the common kernel of two morphisms into group schemes over a field as a closed subscheme of the source, described by its functor of points. It is used in the construction of the relative Picard scheme of two glued smooth curves, where the common kernel of the two restriction maps to the factors is needed as a closed subscheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_comp_eq_one_iff.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_comp_eq_one_iff
    {k : Type u} [Field k] {D D₁ D₂ : Scheme.{u}}
    {d : D ⟶ Spec (CommRingCat.of k)} {d₁ : D₁ ⟶ Spec (CommRingCat.of k)} {d₂ : D₂ ⟶ Spec (CommRingCat.of k)}
    (L₁ : RelativeGroupLaw k d₁) (L₂ : RelativeGroupLaw k d₂)
    (ν₁ : SchemeHomOver d d₁) (ν₂ : SchemeHomOver d d₂) :
    ∃ (K : Scheme.{u}) (j : K ⟶ D), IsClosedImmersion j ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t d),
        (NeronModelInfra.schemeHomOverComp a ν₁ = L₁.one t ∧ NeronModelInfra.schemeHomOverComp a ν₂ = L₂.one t) ↔
          ∃ b : T ⟶ K, b ≫ j = a.1 := by sorry
