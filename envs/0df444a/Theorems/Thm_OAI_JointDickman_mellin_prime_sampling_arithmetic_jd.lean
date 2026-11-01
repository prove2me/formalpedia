-- Prove2me | Theorems.Thm_OAI_JointDickman_mellin_prime_sampling_arithmetic_jd
-- name    : OAI.JointDickman.mellin_prime_sampling_arithmetic_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:28:09.845771+00:00
-- url     : https://prove2.me/theorems/ad1258fc-2689-4101-98b8-f428267a0820
-- title:
--   OAI.JointDickman.mellin_prime_sampling_arithmetic_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.mellin_prime_sampling_arithmetic` of [lean/OAI/NumberTheory/JointDickman/Analysis/MellinPrimeSamplingArithmetic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/MellinPrimeSamplingArithmetic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset TwoPointCorrelations`, `open scoped Classical`):
--
--   ```lean
--   theorem mellin_prime_sampling_arithmetic_jd (B : ℝ) (hB : 1 ≤ B) :
--       ∃ C A δ V : ℝ, 0 < C ∧ 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
--         ∀ (q Z : ℕ) (P Q : Finset ℕ) (N : ℝ) (S : Finset ℝ),
--         16 ≤ q → 2 ≤ Z → Z ≤ q → V ≤ (q:ℝ)^9 →
--         (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 →
--         (∀ p ∈ P, p.Prime ∧ p ≤ Z) →
--         (∀ p ∈ Q, p.Prime ∧ Z < p ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
--         (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
--         (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ (q:ℝ)^B) →
--         ∀ a : ℕ → ℂ,
--         (∑ t ∈ S, ‖mrtExponentialPolynomial Q a (fun n => -Real.log (n:ℝ)) t‖^2) ≤
--           8*(32*C*N*(∏ p ∈ P, (1-1/(p:ℝ))) + (Z+1:ℕ)*
--             (6*(q:ℝ)^9 + (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ))*S.card)*
--               ∑ p ∈ Q, ‖a p‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.TwoPointCorrelations.mrtExponentialPolynomial` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.ramare_product_sparse_integral_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/MellinPrimeSamplingArithmetic.lean (declaration OAI.JointDickman.mellin_prime_sampling_arithmetic)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

theorem mellin_prime_sampling_arithmetic_jd (B : ℝ) (hB : 1 ≤ B) :
    ∃ C A δ V : ℝ, 0 < C ∧ 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (q Z : ℕ) (P Q : Finset ℕ) (N : ℝ) (S : Finset ℝ),
      16 ≤ q → 2 ≤ Z → Z ≤ q → V ≤ (q:ℝ)^9 →
      (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z) →
      (∀ p ∈ Q, p.Prime ∧ Z < p ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ (q:ℝ)^B) →
      ∀ a : ℕ → ℂ,
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q a (fun n => -Real.log (n:ℝ)) t‖^2) ≤
        8*(32*C*N*(∏ p ∈ P, (1-1/(p:ℝ))) + (Z+1:ℕ)*
          (6*(q:ℝ)^9 + (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ))*S.card)*
            ∑ p ∈ Q, ‖a p‖^2 := by
  sorry

end JointDickman

end OAI
end
