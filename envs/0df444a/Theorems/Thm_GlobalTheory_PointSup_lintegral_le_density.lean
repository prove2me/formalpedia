-- Prove2me | Theorems.Thm_GlobalTheory_PointSup_lintegral_le_density
-- name    : GlobalTheory.PointSup.lintegral_le_density
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:02:36.549657+00:00
-- url     : https://prove2.me/theorems/7b5da129-e71c-4254-86c5-f6a7c9f15909
-- title:
--   Point Sup: lintegral le density
-- statement:
--   The Point Sup construction uses the lintegral le density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeDensity.lean#L72-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeDensity.lean#L72-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeDensity
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.PointSup

theorem GlobalTheory.PointSup.lintegral_le_density {n : ℕ} {B O : Set (V n)} (hB : MeasurableSet B) (hBO : B ⊆ O)
    {d : V n → ℝ} {c : ℝ} (hc : 0 < c) (hd : ∀ z ∈ B, c ≤ d z) (g : V n → ℝ≥0∞) :
    ∫⁻ z in B, g z ≤ (ENNReal.ofReal c)⁻¹ *
      ∫⁻ z, g z ∂((volume.restrict O).withDensity fun z => ENNReal.ofReal (d z)) := by sorry
