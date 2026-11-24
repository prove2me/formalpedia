-- Prove2me | Theorems.Thm_GlobalTheory_T_majorant_eq_sum_norm_sq_orthonormalFrame
-- name    : GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:04.537716+00:00
-- url     : https://prove2.me/theorems/a8b6e37b-5443-40b6-bc7f-0f4184acece2
-- title:
--   T: majorant eq sum norm sq orthonormal Frame
-- statement:
--   The T construction uses the majorant eq sum norm sq orthonormal Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajorantEqSumNormSqOrthonormalFrameStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajorantEqSumNormSqOrthonormalFrameStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrame
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrameStatement
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame : (∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → (∀ τ : X.Ψ, (mat x τ).det ≠ 0) ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v = ∑ a, ‖((mat x τ)⁻¹.mulVec v) a‖ ^ 2) := by sorry
