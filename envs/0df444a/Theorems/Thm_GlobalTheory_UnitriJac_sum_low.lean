-- Prove2me | Theorems.Thm_GlobalTheory_UnitriJac_sum_low
-- name    : GlobalTheory.UnitriJac.sum_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:08.256091+00:00
-- url     : https://prove2.me/theorems/c215d1d1-d7e9-4262-8f21-16b8e4fb7f4a
-- title:
--   Unitri Jac: sum low
-- statement:
--   The Unitri Jac construction uses the sum low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L19-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
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
open GlobalTheory GlobalTheory.UnitriJac
open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
noncomputable section

theorem GlobalTheory.UnitriJac.sum_low {r : ℕ} (u : Low r → ℂ) (f : Fin r → Fin r → ℂ) :
    ∑ q : Low r, f q.1.1 q.1.2 * u q = ∑ a, ∑ c, f a c * lowMat u a c := by sorry
