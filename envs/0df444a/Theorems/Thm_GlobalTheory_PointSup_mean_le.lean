-- Prove2me | Theorems.Thm_GlobalTheory_PointSup_mean_le
-- name    : GlobalTheory.PointSup.mean_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:58.843655+00:00
-- url     : https://prove2.me/theorems/ac6729a7-baf4-4922-9833-76746782df23
-- title:
--   Point Sup: mean le
-- statement:
--   The Point Sup construction uses the mean le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeDensity.lean#L51-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeDensity.lean#L51-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeDensity
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

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

theorem GlobalTheory.PointSup.mean_le {n : ℕ} {R : ℝ} {u : V n → ℂ} (hu : DifferentiableOn ℂ u (Metric.ball 0 R))
    {g : V n → ℝ≥0∞} (hg : Measurable g) {J A : ℝ≥0∞} (hJ : J < ⊤)
    (hgJ : ∫⁻ z in Metric.ball (0 : V n) R, g z ≤ J)
    (hpt : ∀ z ∈ Metric.ball (0 : V n) R, g z < ⊤ → ENNReal.ofReal (‖u z‖ ^ 2) ≤ g z * A) :
    ENNReal.ofReal ‖u 0‖ ^ 2 * volume (Metric.ball (0 : V n) R) ≤ J * A := by sorry
