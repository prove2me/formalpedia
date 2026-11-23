-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryLift_conj_unitary
-- name    : GlobalTheory.UnitaryLift.conj_unitary
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:32.814316+00:00
-- url     : https://prove2.me/theorems/4e0b2626-4abc-43dd-8dd0-152c405fdbfd
-- title:
--   Unitary Lift: conj unitary
-- statement:
--   The Unitary Lift construction uses the conj unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FrameStepOfRightMulRealUnitaryGroup.lean#L14-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FrameStepOfRightMulRealUnitaryGroup.lean#L14-L44

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

theorem GlobalTheory.UnitaryLift.conj_unitary {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0)
    (c : X.Ψ → GL (Fin r) ℂ)
    (hc : ∀ τ, (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) *
      (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) :
    X.IsUnitaryC fun τ =>
      ((toGL X hx0 * c * (toGL X hx0)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by sorry
