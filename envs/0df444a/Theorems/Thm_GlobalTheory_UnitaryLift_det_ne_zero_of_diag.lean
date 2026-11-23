-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryLift_det_ne_zero_of_diag
-- name    : GlobalTheory.UnitaryLift.det_ne_zero_of_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:19.898511+00:00
-- url     : https://prove2.me/theorems/82f1433c-74bf-40d5-a295-b2b34690020f
-- title:
--   Unitary Lift: det ne zero of diag
-- statement:
--   The Unitary Lift construction uses the det ne zero of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FrameStepOfRightMulRealUnitaryGroup.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FrameStepOfRightMulRealUnitaryGroup.lean#L49-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FrameStepOfRightMulRealUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.UnitaryLift
open GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UnitaryLift.det_ne_zero_of_diag {r p : ℕ} {a : Matrix (Fin r) (Fin r) ℂ}
    (ha : aᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) *
      a.map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1)) : a.det ≠ 0 := by sorry
