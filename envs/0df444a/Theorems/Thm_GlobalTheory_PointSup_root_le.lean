-- Prove2me | Theorems.Thm_GlobalTheory_PointSup_root_le
-- name    : GlobalTheory.PointSup.root_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:00:49.296401+00:00
-- url     : https://prove2.me/theorems/e7ed766b-c185-5147-bf2b-a514dea31d15
-- title:
--   Point Sup: root le
-- statement:
--   The Point Sup construction uses the root le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeDensity.lean#L95-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeDensity.lean#L95-L109

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

theorem GlobalTheory.PointSup.root_le {a S J v : ℝ≥0∞} {K k : ℝ} (hJ : J < ⊤) (hv : v ≠ 0) (hvt : v ≠ ⊤) (hK : 0 ≤ K)
    (hk : 0 ≤ k) (h : a ^ 2 * v ≤ J * (ENNReal.ofReal (K * k) * S ^ 2)) :
    a ≤ ENNReal.ofReal (Real.sqrt ((J / v).toReal * K) * Real.sqrt k) * S := by sorry
