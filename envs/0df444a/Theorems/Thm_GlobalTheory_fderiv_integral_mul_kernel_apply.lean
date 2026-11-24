-- Prove2me | Theorems.Thm_GlobalTheory_fderiv_integral_mul_kernel_apply
-- name    : GlobalTheory.fderiv_integral_mul_kernel_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:29.6668+00:00
-- url     : https://prove2.me/theorems/8fb96b9a-6d79-464b-8852-bacc42963ce7
-- title:
--   Global Theory: fderiv integral mul kernel apply
-- statement:
--   The Global Theory construction uses the fderiv integral mul kernel apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FderivIntegralMulKernelApply.lean#L7-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FderivIntegralMulKernelApply.lean#L7-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FderivIntegralMulKernelApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.fderiv_integral_mul_kernel_apply :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
      [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] {U : Set V}, IsOpen U →
      ∀ {α : V → ℂ}, Continuous α → HasCompactSupport α → tsupport α ⊆ U →
      ∀ {K : V × V → ℂ}, ContDiffOn ℝ ∞ K (U ×ˢ U) → ∀ {x : V}, x ∈ U → ∀ v : V,
      fderiv ℝ (fun x' => ∫ y, α y * K (x', y) ∂ν) x v =
        ∫ y, α y * fderiv ℝ (fun x' => K (x', y)) x v ∂ν := by sorry
