-- Prove2me | Theorems.Thm_GlobalTheory_EvalNormCoefficientBound_norm_eval_le_sum_norm_coeff
-- name    : GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:20.28121+00:00
-- url     : https://prove2.me/theorems/1b5c05ed-c8cc-47cd-ad25-ab59af0f9c1b
-- title:
--   Eval Norm Coefficient Bound: norm eval le sum norm coeff
-- statement:
--   The Eval Norm Coefficient Bound construction uses the norm eval le sum norm coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEvalLeSumNormCoeff.lean#L5-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEvalLeSumNormCoeff.lean#L5-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEvalLeSumNormCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EvalNormCoefficientBound

theorem GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ)
    (hv : ∀ (s : σ), ‖v s‖ ≤ (1 : ℝ)) :
    ‖(MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P‖ ≤
      ∑ d ∈ MvPolynomial.support P, ‖MvPolynomial.coeff d P‖ := by sorry
