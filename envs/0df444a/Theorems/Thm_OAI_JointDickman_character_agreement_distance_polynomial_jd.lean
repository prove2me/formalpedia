-- Prove2me | Theorems.Thm_OAI_JointDickman_character_agreement_distance_polynomial_jd
-- name    : OAI.JointDickman.character_agreement_distance_polynomial_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:25:16.494931+00:00
-- url     : https://prove2.me/theorems/63095772-0541-4007-8ddd-40f6532f48cb
-- title:
--   OAI.JointDickman.character_agreement_distance_polynomial_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.character_agreement_distance_polynomial` of [lean/OAI/NumberTheory/JointDickman/Analysis/CharacterPolynomialDistance.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/CharacterPolynomialDistance.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Complex Filter Finset PublishedInputs`, `open scoped Topology`):
--
--   ```lean
--   theorem character_agreement_distance_polynomial_jd {q : ℕ} [NeZero q]
--       (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
--       (P : Finset ℕ) (A : ℝ) (hA : 1 ≤ A) (R : ℝ) :
--       ∀ᶠ X : ℝ in atTop, ∀ f : ArithmeticFunction ℂ,
--         (∀ n, ‖f n‖ ≤ 1) →
--         (∀ p : ℕ, p.Prime → p ∉ P → (p:ℝ) ≤ X^c → f p = χ p) →
--         ∀ t : ℝ, |t| ≤ X^A → R ≤ primeDistanceSquared f X t
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.PublishedInputs.primeDistanceSquared` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.twisted_auxiliary_cofactor_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/CharacterPolynomialDistance.lean (declaration OAI.JointDickman.character_agreement_distance_polynomial)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Complex Filter Finset PublishedInputs
open scoped Topology

theorem character_agreement_distance_polynomial_jd {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (P : Finset ℕ) (A : ℝ) (hA : 1 ≤ A) (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ f : ArithmeticFunction ℂ,
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ P → (p:ℝ) ≤ X^c → f p = χ p) →
      ∀ t : ℝ, |t| ≤ X^A → R ≤ primeDistanceSquared f X t := by
  sorry

end JointDickman

end OAI
end
