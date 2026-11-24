-- Prove2me | Theorems.Thm_GlobalTheory_UnitriJac_adM_mulVec
-- name    : GlobalTheory.UnitriJac.adM_mulVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:48:09.32556+00:00
-- url     : https://prove2.me/theorems/7c999e81-7f31-4d5f-8164-2951b56dac03
-- title:
--   Unitri Jac: ad M mul Vec
-- statement:
--   The Unitri Jac construction uses the ad M mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L46-L54

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

theorem GlobalTheory.UnitriJac.adM_mulVec {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (u : Low r → ℂ) (p : Low r) :
    (adM B *ᵥ u) p = (B * lowMat u * B⁻¹) p.1.1 p.1.2 := by sorry
