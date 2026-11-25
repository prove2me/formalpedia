-- Prove2me | Theorems.Thm_GlobalTheory_PointSup_point_le
-- name    : GlobalTheory.PointSup.point_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:38.350648+00:00
-- url     : https://prove2.me/theorems/0adf5f12-6833-5120-9caa-35ea8b629089
-- title:
--   Point Sup: point le
-- statement:
--   The Point Sup construction uses the point le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeDensity.lean#L12-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeDensity.lean#L12-L49

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

theorem GlobalTheory.PointSup.point_le {p k K e c : ℝ} {w S : ℝ≥0∞} (hk : 0 < k) (hkK : k ≤ K) (hc : 0 < c) (hce : c ≤ e)
    (hw : w ≠ 0) (hS : (ENNReal.ofReal e / w) ^ (1 / 2 : ℝ) ≤ S)
    (hfin : ENNReal.ofReal p * w * ENNReal.ofReal k⁻¹ < ⊤) :
    ENNReal.ofReal p ≤
      ENNReal.ofReal p * w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2) := by sorry
