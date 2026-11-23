-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryLift_step_of_right_mul
-- name    : GlobalTheory.UnitaryLift.step_of_right_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:39.343426+00:00
-- url     : https://prove2.me/theorems/2ffef766-49b2-493c-bb4d-eb3b5628d2b1
-- title:
--   Unitary Lift: step of right mul
-- statement:
--   The Unitary Lift construction uses the step of right mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FrameStepOfRightMulRealUnitaryGroup.lean#L102-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FrameStepOfRightMulRealUnitaryGroup.lean#L102-L175

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

theorem GlobalTheory.UnitaryLift.step_of_right_mul :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∀ (τ0 : X.Ψ) (a s : Matrix (Fin r) (Fin r) ℂ), (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → s * a = a⁻¹ * s → ∃ h k : H, k * h = h⁻¹ * k ∧ ∀ g : H, (X.lmulC (fun τ => (((g * h : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by sorry
