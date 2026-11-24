-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_redKer_ext
-- name    : GlobalTheory.SqZero.redKer_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:17.007797+00:00
-- url     : https://prove2.me/theorems/e721211a-949b-4564-bb81-f3a600202bd7
-- title:
--   Sq Zero: red Ker ext
-- statement:
--   The Sq Zero construction uses the red Ker ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsChartOfMemRedKer.lean#L181-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsChartOfMemRedKer.lean#L181-L219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {A A' A₀ : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  [CommRing A₀] [Algebra R A₀]
variable {G}

theorem GlobalTheory.SqZero.redKer_ext {J : Ideal A} (hJ : J ^ 2 = ⊥) {y y' : sp A ⟶ G} (hy : y ∈ redKer G J)
    (hy' : y' ∈ redKer G J) (q₁ : A →ₐ[R] A') (q₂ : A →ₐ[R] A₀)
    (hq : ∀ a, q₁ a = 0 → q₂ a = 0 → a = 0) (h₁ : spMap q₁ ≫ y = spMap q₁ ≫ y')
    (h₂ : spMap q₂ ≫ y = spMap q₂ ≫ y') : y = y' := by sorry
