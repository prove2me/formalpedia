-- Prove2me | Theorems.Thm_GlobalTheory_JetsPure_main
-- name    : GlobalTheory.JetsPure.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:50.032345+00:00
-- url     : https://prove2.me/theorems/d5ffabc6-87ec-5a34-8ed9-08a8e02352a8
-- title:
--   Jets Pure: main
-- statement:
--   The Jets Pure construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/SumMultiLtSucc.lean#L29-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/SumMultiLtSucc.lean#L29-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_PointwiseNormConstantSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SumMultiLtSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.JetsPure
open Filter Asymptotics
open MeasureTheory Topology Filter Asymptotics
open scoped ContDiff ENNReal Matrix

theorem GlobalTheory.JetsPure.main : ∀ (J I : Type) [Fintype I] (D T a : ℕ),
    a ≤ T + 1 → ∀ (n : J → ℕ) (e : ∀ p, Fin (n p) ≃ Fin D)
    (f w0 : ∀ p, _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ) (s : ∀ p, Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ)
    (t : ∀ p, I → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ),
    (∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), DifferentiableAt ℂ (f p) z ∧
      DifferentiableAt ℂ (w0 p) z ∧
      (∀ k, DifferentiableAt ℂ (s p k) z) ∧ ∀ k, DifferentiableAt ℂ (t p k) z) →
    (∀ p, w0 p 0 ≠ 0 ∧ (∀ k, s p k 0 = 0) ∧
      (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) 0).det
        ≠ 0) →
    (∀ v : J → ℂ, ∃ u : I → ℂ, ∀ p, ∑ k, u k * t p k 0 = v p) →
    ∃ cc : (Fin D → ℕ) → I → ℂ, ∀ p, (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
      cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) =O[𝓝 0]
        fun z => ‖z‖ ^ a := by sorry
