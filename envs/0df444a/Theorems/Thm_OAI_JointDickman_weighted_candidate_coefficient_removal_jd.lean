-- Prove2me | Theorems.Thm_OAI_JointDickman_weighted_candidate_coefficient_removal_jd
-- name    : OAI.JointDickman.weighted_candidate_coefficient_removal_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:36:25.821829+00:00
-- url     : https://prove2.me/theorems/a50557a2-742f-4de0-abb8-02b4f74476a2
-- title:
--   OAI.JointDickman.weighted_candidate_coefficient_removal_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.weighted_candidate_coefficient_removal` of [lean/OAI/NumberTheory/JointDickman/Amplification/WeightedCandidateComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/WeightedCandidateComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology`, `open Classical in`):
--
--   ```lean
--   theorem weighted_candidate_coefficient_removal_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput) :
--       ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
--         ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
--           ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, 0 < T → Real.log T ≤ (B : ℝ)/10 →
--             ∀ (C : ℝ) (j U V : ℕ), 0 ≤ C → 0 < j → (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
--             (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
--               ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
--             (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
--               ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
--             ∀ q : ℕ → ℕ → ℝ, (∀ a b, |q a b| ≤ 1) →
--             ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
--             (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
--             |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
--                 (retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L j τ C T V q))-
--               weightedAmplificationArithmeticSum B j T U V q h g| ≤
--               ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
--                 K/T*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryCutoff`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.coefficientScale`, `OAI.JointDickman.dyadicBoxIndices`, `OAI.JointDickman.dyadicBoxLower`, `OAI.JointDickman.dyadicBoxUpper`, `OAI.JointDickman.retainedSubsetKernel`, `OAI.JointDickman.singularFactor`, `OAI.JointDickman.subsetSiteTest`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.subsetKernelBilinear`, `OAI.JointDickman.weightedAmplificationArithmeticSum` and `OAI.JointDickman.weightedCandidateRetained` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.counting_block_test_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/WeightedCandidateComparison.lean (declaration OAI.JointDickman.weighted_candidate_coefficient_removal)

import Mathlib
import Definitions.Def_OAIQ083J003

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem weighted_candidate_coefficient_removal_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, 0 < T → Real.log T ≤ (B : ℝ)/10 →
          ∀ (C : ℝ) (j U V : ℕ), 0 ≤ C → 0 < j → (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ q : ℕ → ℕ → ℝ, (∀ a b, |q a b| ≤ 1) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
              (retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L j τ C T V q))-
            weightedAmplificationArithmeticSum B j T U V q h g| ≤
            ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              K/T*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  sorry

end JointDickman

end OAI
end
