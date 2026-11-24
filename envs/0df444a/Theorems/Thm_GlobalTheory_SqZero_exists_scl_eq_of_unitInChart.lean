-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_exists_scl_eq_of_unitInChart
-- name    : GlobalTheory.SqZero.exists_scl_eq_of_unitInChart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:22:45.822804+00:00
-- url     : https://prove2.me/theorems/0b5243e6-6244-46ee-81e3-3ac59c4f9b41
-- title:
--   Sq Zero: exists scl eq of unit In Chart
-- statement:
--   The Sq Zero construction uses the exists scl eq of unit In Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsResEqOfUnitInChart.lean#L259-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsResEqOfUnitInChart.lean#L259-L286

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
variable [Smooth G.hom] {ρ : S →ₐ[R] S'} {g : S}

theorem GlobalTheory.SqZero.exists_scl_eq_of_unitInChart (hS : UnitInChart G S) (hρ : IsAway ρ g)
    {w w' : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (hw' : IsTanOver w')
    (h : res ρ w = res ρ w') : ∃ N : ℕ, scl (g ^ N) w = scl (g ^ N) w' := by sorry
