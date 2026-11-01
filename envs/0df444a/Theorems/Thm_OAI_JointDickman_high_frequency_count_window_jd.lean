-- Prove2me | Theorems.Thm_OAI_JointDickman_high_frequency_count_window_jd
-- name    : OAI.JointDickman.high_frequency_count_window_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:16:27.852347+00:00
-- url     : https://prove2.me/theorems/4494b3cb-db1a-4ba9-9803-1db472a4cd2a
-- title:
--   OAI.JointDickman.high_frequency_count_window_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.high_frequency_count_window` of [lean/OAI/NumberTheory/JointDickman/Counting/HighCofactorWindow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/HighCofactorWindow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter TwoPointCorrelations`, `open scoped Topology`):
--
--   ```lean
--   theorem high_frequency_count_window_jd {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
--       (E : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
--       ∃ K : ℕ, 2 ≤ K ∧ ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
--         ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
--         (∀ p : ℕ, p.Prime → p ∉ E → (p:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c → f p = 1) →
--         ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
--         ∀ t : ℝ, 2*(Real.log (⌊(2*N:ℝ)/a⌋₊:ℝ))^8 ≤ |t| →
--           |t| ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 →
--           ‖mrtCofactorPolynomial P (mrtMissingCoefficient f Q) N a t‖ ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.TwoPointCorrelations.mrtCofactorPolynomial` and `OAI.TwoPointCorrelations.mrtMissingCoefficient` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.bin_auxiliary_cofactor_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/HighCofactorWindow.lean (declaration OAI.JointDickman.high_frequency_count_window)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

theorem high_frequency_count_window_jd {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ E → (p:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c → f p = 1) →
      ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
      ∀ t : ℝ, 2*(Real.log (⌊(2*N:ℝ)/a⌋₊:ℝ))^8 ≤ |t| →
        |t| ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 →
        ‖mrtCofactorPolynomial P (mrtMissingCoefficient f Q) N a t‖ ≤ ε := by
  sorry

end JointDickman

end OAI
end
