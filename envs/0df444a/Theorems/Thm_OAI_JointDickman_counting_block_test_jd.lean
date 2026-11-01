-- Prove2me | Theorems.Thm_OAI_JointDickman_counting_block_test_jd
-- name    : OAI.JointDickman.counting_block_test_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:33:09.180217+00:00
-- url     : https://prove2.me/theorems/f1ebe798-c9d7-4e42-a894-d535c0c4b355
-- title:
--   OAI.JointDickman.counting_block_test_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.counting_block_test` of [lean/OAI/NumberTheory/JointDickman/Counting/CountingBlockTest.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingBlockTest.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter Classical PublishedInputs`, `open scoped Topology`):
--
--   ```lean
--   theorem counting_block_test_jd
--       (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
--       (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
--       (hMP : PrimeProductMertensInput) {L : ℕ} {τ η w δ : ℝ} (hL : 0 < L) (hτ : 0 < τ)
--       (hη : 0 < η) (hw : 0 < w) (hδ : 0 < δ) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∃ P : MvPolynomial (Fin 4) ℝ,
--         ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
--         (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
--         ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
--         ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
--         ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V Q : ℕ),
--           0 ≤ C → 0 < T → T ≤ amplificationMultiplier B → Real.log T ≤ (B : ℝ)/10 →
--           (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
--           (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
--             ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
--           (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
--             ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
--           0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → T*Q ≤ B → η*T ≤ H → T ≤ M →
--           ∀ σ : ℝ, |σ| ≤ 3 →
--           (∀ j : ℕ, H < j → j < T →
--             ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀) ∧
--           (∀ g h : Fin M → (auxiliaryPrimes B).powerset → ℝ,
--             (∀ i a, |g i a| ≤ 1) → (∀ i a, |h i a| ≤ 1) →
--             siteTestMean (fun _ : Fin M => independentPrimeSetMass B)
--               (countingSiteError P m B L T H M τ C w c D σ) g h ≤
--               (M : ℝ)*(2*(ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ)*Real.exp 24))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.amplificationMultiplier`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.countingPrimeKernel`, `OAI.JointDickman.countingSiteError`, `OAI.JointDickman.dyadicBoxIndices`, `OAI.JointDickman.dyadicBoxLower`, `OAI.JointDickman.dyadicBoxUpper`, `OAI.JointDickman.independentPrimeSetMass`, `OAI.JointDickman.squarefreeLeadingConstant`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.siteTestMean` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.counting_sampling_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingBlockTest.lean (declaration OAI.JointDickman.counting_block_test)

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
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_block_test_jd
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) {L : ℕ} {τ η w δ : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (hη : 0 < η) (hw : 0 < w) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V Q : ℕ),
        0 ≤ C → 0 < T → T ≤ amplificationMultiplier B → Real.log T ≤ (B : ℝ)/10 →
        (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → T*Q ≤ B → η*T ≤ H → T ≤ M →
        ∀ σ : ℝ, |σ| ≤ 3 →
        (∀ j : ℕ, H < j → j < T →
          ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀) ∧
        (∀ g h : Fin M → (auxiliaryPrimes B).powerset → ℝ,
          (∀ i a, |g i a| ≤ 1) → (∀ i a, |h i a| ≤ 1) →
          siteTestMean (fun _ : Fin M => independentPrimeSetMass B)
            (countingSiteError P m B L T H M τ C w c D σ) g h ≤
            (M : ℝ)*(2*(ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ)*Real.exp 24)) := by
  sorry

end JointDickman

end OAI
end
