-- Prove2me | Theorems.Thm_GlobalTheory_UnitriJac_leftM_mulVec
-- name    : GlobalTheory.UnitriJac.leftM_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:18.057833+00:00
-- url     : https://prove2.me/theorems/6a947089-7243-4f4e-9542-4d5cb43b6854
-- title:
--   Unitri Jac: left M mul Vec
-- statement:
--   The Unitri Jac construction uses the left M mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L39-L44

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

theorem GlobalTheory.UnitriJac.leftM_mulVec {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (u : Low r → ℂ) (p : Low r) :
    (leftM N *ᵥ u) p = (N * lowMat u) p.1.1 p.1.2 := by sorry
