-- Prove2me | Theorems.Thm_OAI_JointDickman_counting_arithmetic_feature_comparison_jd
-- name    : OAI.JointDickman.counting_arithmetic_feature_comparison_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:25:25.346207+00:00
-- url     : https://prove2.me/theorems/98b8d2a9-59d6-47b8-ba2c-c7593469e15d
-- title:
--   OAI.JointDickman.counting_arithmetic_feature_comparison_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.counting_arithmetic_feature_comparison` of [lean/OAI/NumberTheory/JointDickman/Counting/CountingArithmeticFeatures.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingArithmeticFeatures.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem counting_arithmetic_feature_comparison_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput)
--       {η w : ℝ} (hη : 0 < η) (hw : 0 < w) :
--       ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 4) ℝ,
--         ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
--         (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
--         ∃ H m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
--         ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
--         ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
--         ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
--         ∀ σ : ℝ, |σ| ≤ 3 →
--         ∀ U V : ℕ,
--         (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
--           ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
--         (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
--           ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
--         ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
--         (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
--         T*|rampedAmplificationArithmeticSum B j T U V w σ g h-
--           (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
--             fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
--               countingPrimeKernel P m B j c H T σ x y)| ≤ ε B+δ*(T/j)*singularSeries j ∧
--           ∀ x y, |countingPrimeKernel P m B j c H T σ x y| ≤ C₀
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.countingPrimeKernel`, `OAI.JointDickman.dyadicBoxIndices`, `OAI.JointDickman.dyadicBoxLower`, `OAI.JointDickman.dyadicBoxUpper`, `OAI.JointDickman.fullPrimeMass`, `OAI.JointDickman.rampedAmplificationArithmeticSum`, `OAI.JointDickman.singularSeries`, `OAI.JointDickman.squarefreeLeadingConstant`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.counting_block_test_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingArithmeticFeatures.lean (declaration OAI.JointDickman.counting_arithmetic_feature_comparison)

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

theorem counting_arithmetic_feature_comparison_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {η w : ℝ} (hη : 0 < η) (hw : 0 < w) :
    ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
      ∀ σ : ℝ, |σ| ≤ 3 →
      ∀ U V : ℕ,
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|rampedAmplificationArithmeticSum B j T U V w σ g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
            countingPrimeKernel P m B j c H T σ x y)| ≤ ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |countingPrimeKernel P m B j c H T σ x y| ≤ C₀ := by
  sorry

end JointDickman

end OAI
end
