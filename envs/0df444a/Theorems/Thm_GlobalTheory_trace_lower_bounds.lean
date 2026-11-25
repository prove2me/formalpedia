-- Prove2me | Theorems.Thm_GlobalTheory_trace_lower_bounds
-- name    : GlobalTheory.trace_lower_bounds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:05.988074+00:00
-- url     : https://prove2.me/theorems/983e9caf-93e1-5848-8172-70da45c09f18
-- title:
--   Global Theory: trace lower bounds
-- statement:
--   The Global Theory construction uses the trace lower bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L255-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L255-L278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.trace_lower_bounds (F K : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    [Field K] [NumberField K] :
    (∀ a : F, (∀ σ : F →+* ℝ, 0 < σ a) →
      (finrank ℚ F : ℝ) * ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (1 / (finrank ℚ F : ℝ))
        ≤ ((Algebra.trace ℚ F a : ℚ) : ℝ)) ∧
    (∀ a : F, IsIntegral ℤ a → (∀ σ : F →+* ℝ, 0 < σ a) →
      (finrank ℚ F : ℚ) ≤ Algebra.trace ℚ F a) ∧
    (∀ a : K, IsIntegral ℤ a → ∑ σ : K →+* ℂ, ‖σ a‖ < finrank ℚ K → a = 0) ∧
    (∀ x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹, x ≠ 0 →
      (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
        ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2) ∧
    (∀ (J : FractionalIdeal (𝓞 K)⁰ K), ∀ x ∈ J, x ≠ 0 →
      (finrank ℚ K : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ (2 / (finrank ℚ K : ℝ))
        ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2) ∧
    (∀ (a : F) (σ : F →+* ℝ), σ a = 0 → a = 0) ∧
    (∀ q : ℚ, q ≠ 0 → ∀ x ∈ Submodule.traceDual ℤ ℚ (Submodule.span (𝓞 F) {(q : F)}),
      ∃ m : ℤ, Algebra.trace ℚ F x = q⁻¹ * m) := by sorry
