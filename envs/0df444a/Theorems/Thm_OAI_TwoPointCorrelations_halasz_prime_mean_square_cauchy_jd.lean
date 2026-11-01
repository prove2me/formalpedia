-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_mean_square_cauchy_jd
-- name    : OAI.TwoPointCorrelations.halasz_prime_mean_square_cauchy_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:30:30.110738+00:00
-- url     : https://prove2.me/theorems/e7cae54b-53a5-41c8-b0d3-beada1ec5c89
-- title:
--   OAI.TwoPointCorrelations.halasz_prime_mean_square_cauchy_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TwoPointCorrelations.halasz_prime_mean_square_cauchy` of [lean/OAI/NumberTheory/TwoPointCorrelations/HalaszCauchyMeanSquare.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TwoPointCorrelations/HalaszCauchyMeanSquare.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TwoPointCorrelations`, with `open Finset MeasureTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem halasz_prime_mean_square_cauchy_jd : ∃ C : ℝ, 0 < C ∧
--       ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ a : ℕ → ℂ,
--         (∫ t : ℝ, ‖mrtExponentialPolynomial P
--           (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
--           (fun p => -Real.log (p : ℝ)) t‖ ^ 2 * (1 + t ^ 2)⁻¹) ≤
--           C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TwoPointCorrelations.mrtExponentialPolynomial` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.TwoPointCorrelations.halasz_prime_window_middle_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TwoPointCorrelations/HalaszCauchyMeanSquare.lean (declaration OAI.TwoPointCorrelations.halasz_prime_mean_square_cauchy)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem halasz_prime_mean_square_cauchy_jd : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ a : ℕ → ℂ,
      (∫ t : ℝ, ‖mrtExponentialPolynomial P
        (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖ ^ 2 * (1 + t ^ 2)⁻¹) ≤
        C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p) := by
  sorry

end TwoPointCorrelations

end OAI
end
