-- Prove2me | Theorems.Thm_GlobalTheory_UnitriJac_lowMat_leftM
-- name    : GlobalTheory.UnitriJac.lowMat_leftM
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:47.782546+00:00
-- url     : https://prove2.me/theorems/ee7cf3a3-8c3f-49f4-803e-36b992852181
-- title:
--   Unitri Jac: low Mat left M
-- statement:
--   The Unitri Jac construction uses the low Mat left M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L56-L68

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

theorem GlobalTheory.UnitriJac.lowMat_leftM {r : ℕ} {N : Matrix (Fin r) (Fin r) ℂ} (hN : LowU N) (u : Low r → ℂ) :
    lowMat (leftM N *ᵥ u) = N * lowMat u := by sorry
