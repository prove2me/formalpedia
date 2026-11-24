-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_exists_chart_of_isTanOver
-- name    : GlobalTheory.SqZero.exists_chart_of_isTanOver
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:51.966694+00:00
-- url     : https://prove2.me/theorems/3bb1084f-a9ec-4f04-a4be-8ecb9c59b8af
-- title:
--   Sq Zero: exists chart of is Tan Over
-- statement:
--   The Sq Zero construction uses the exists chart of is Tan Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsResEqOfUnitInChart.lean#L235-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsResEqOfUnitInChart.lean#L235-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
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
variable {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S'']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem GlobalTheory.SqZero.exists_chart_of_isTanOver {B : Type} [CommRing B] [Algebra R B] (j : sp B ⟶ G)
    [IsOpenImmersion j.left] (u : B →ₐ[R] S) (hu : spMap u ≫ j = 1)
    {w : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) :
    ∃ φ : B →ₐ[R] DualNumber S, w = spMap φ ≫ j ∧ ∀ b, (φ b).fst = u b := by sorry
