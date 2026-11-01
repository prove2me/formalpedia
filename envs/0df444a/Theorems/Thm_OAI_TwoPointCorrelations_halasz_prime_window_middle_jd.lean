-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_window_middle_jd
-- name    : OAI.TwoPointCorrelations.halasz_prime_window_middle_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:30:35.034861+00:00
-- url     : https://prove2.me/theorems/7c528f9d-6d5a-45cf-ac6f-32d3d15e3c6e
-- title:
--   OAI.TwoPointCorrelations.halasz_prime_window_middle_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TwoPointCorrelations.halasz_prime_window_middle` of [lean/OAI/NumberTheory/TwoPointCorrelations/HalaszWindowIntegral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TwoPointCorrelations/HalaszWindowIntegral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TwoPointCorrelations`, with `open Complex MeasureTheory Finset`):
--
--   ```lean
--   theorem halasz_prime_window_middle_jd : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
--       ∀ (x δ T A : ℝ), 0 < x → 0 < δ → δ ≤ 1 → B ≤ T → 0 ≤ A →
--       ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
--         (∀ q ∈ Q, q.Prime) → ∀ (a b : ℕ → ℂ) (F : ℝ → ℂ),
--         (∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ A) →
--         ‖∫ t in -T..T,
--           mrtExponentialPolynomial P (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
--             (fun p => -Real.log (p : ℝ)) t *
--           mrtExponentialPolynomial Q (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ))
--             (fun q => -Real.log (q : ℝ)) t * F t *
--           halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
--           (C * x * A) * (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
--             Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TwoPointCorrelations.mrtExponentialPolynomial` (definitions bundle `OAIQ083J001` of this split); `OAI.TwoPointCorrelations.halaszPerronWindowKernel` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.high_frequency_count_window_jd` and `OAI.JointDickman.twisted_auxiliary_cofactor_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TwoPointCorrelations/HalaszWindowIntegral.lean (declaration OAI.TwoPointCorrelations.halasz_prime_window_middle)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TwoPointCorrelations

open Complex MeasureTheory Finset

theorem halasz_prime_window_middle_jd : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (x δ T A : ℝ), 0 < x → 0 < δ → δ ≤ 1 → B ≤ T → 0 ≤ A →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ (a b : ℕ → ℂ) (F : ℝ → ℂ),
      (∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ A) →
      ‖∫ t in -T..T,
        mrtExponentialPolynomial P (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t *
        mrtExponentialPolynomial Q (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ))
          (fun q => -Real.log (q : ℝ)) t * F t *
        halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
        (C * x * A) * (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) := by
  sorry

end TwoPointCorrelations

end OAI
end
