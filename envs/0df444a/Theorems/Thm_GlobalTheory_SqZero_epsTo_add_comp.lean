-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_epsTo_add_comp
-- name    : GlobalTheory.SqZero.epsTo_add_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:05.340955+00:00
-- url     : https://prove2.me/theorems/1677b7ee-75b0-427b-8afd-5dac05d2e110
-- title:
--   Sq Zero: eps To add comp
-- statement:
--   The Sq Zero construction uses the eps To add comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsChartOfMemRedKer.lean#L231-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsChartOfMemRedKer.lean#L231-L278

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

theorem GlobalTheory.SqZero.epsTo_add_comp {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (t₁ t₂ : A)
    (h₁ : t₁ * t₁ = 0) (h₂ : t₂ * t₂ = 0) (h₁₂ : t₁ * t₂ = 0) (h : (t₁ + t₂) * (t₁ + t₂) = 0) :
    spMap (epsTo R (t₁ + t₂) h) ≫ w =
      (spMap (epsTo R t₁ h₁) ≫ w) * (spMap (epsTo R t₂ h₂) ≫ w) := by sorry
