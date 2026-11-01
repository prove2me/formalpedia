-- Prove2me | Theorems.Thm_OAI_JointDickman_weightedAmplification_second_bound_jd
-- name    : OAI.JointDickman.weightedAmplification_second_bound_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:30:00.783928+00:00
-- url     : https://prove2.me/theorems/94a87c27-7ecf-4572-8f2f-4096521a2556
-- title:
--   OAI.JointDickman.weightedAmplification_second_bound_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.weightedAmplification_second_bound` of [lean/OAI/NumberTheory/JointDickman/Amplification/WeightedAmplification.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/WeightedAmplification.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem weightedAmplification_second_bound_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput) :
--       ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
--         ∀ (T : ℕ) (w : ℕ → ℕ → ℝ), 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
--         (∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) →
--         (∀ a c, (a, c) ∉ amplificationCoefficientPairs B T → w a c = 0) →
--         (∑ S ∈ (auxiliaryPrimes B).powerset,
--           bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
--         ∑ R ∈ (auxiliaryPrimes B).powerset,
--           bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
--           (independentWeightedAmplification B L τ C w S R)^2) ≤ K
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.amplificationCoefficientPairs`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.bernoulliSubsetMass`, `OAI.JointDickman.independentWeightedAmplification`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy_jd` and `OAI.JointDickman.rationalFixedScaleLaw_of_distance_divergence_proved_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/WeightedAmplification.lean (declaration OAI.JointDickman.weightedAmplification_second_bound)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem weightedAmplification_second_bound_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (T : ℕ) (w : ℕ → ℕ → ℝ), 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) →
      (∀ a c, (a, c) ∉ amplificationCoefficientPairs B T → w a c = 0) →
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
      ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
        (independentWeightedAmplification B L τ C w S R)^2) ≤ K := by
  sorry

end JointDickman

end OAI
end
