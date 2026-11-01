-- Prove2me | Theorems.Thm_OAI_JointDickman_counting_sampling_actual_scale_jd
-- name    : OAI.JointDickman.counting_sampling_actual_scale_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:27:08.391211+00:00
-- url     : https://prove2.me/theorems/bc52a679-59ef-4d58-8328-5dfd9552d14a
-- title:
--   OAI.JointDickman.counting_sampling_actual_scale_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.counting_sampling_actual_scale` of [lean/OAI/NumberTheory/JointDickman/Counting/CountingSamplingScale.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingSamplingScale.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter Classical PublishedInputs`, `open scoped Topology`):
--
--   ```lean
--   theorem counting_sampling_actual_scale_jd
--       (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
--       (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
--       (hMP : PrimeProductMertensInput) (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
--       {L A : ℕ} {cap : ℝ} (hL : 10000 ≤ L) (hA : 0 < A) (hcap : 0 < cap) :
--       ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
--         ∀ w ε : ℝ, 0 < w → 0 < ε →
--         ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
--         (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
--         ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
--         ∃ Cmin Kerror : ℝ, 0 ≤ Cmin ∧ 0 ≤ Kerror ∧
--         ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, Cmin ≤ C →
--         ∀ J : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
--           (∑ u ∈ range (J*N), countingArithmeticCutError P m B L (amplificationMultiplier B)
--             (amplificationMultiplier B/A) (A*amplificationMultiplier B) τ C w c D
--             (countingOriginParameter (amplificationMultiplier B) N u) u)/(N : ℝ) <
--             (J : ℝ)*(ε+Kerror/(B : ℝ))+δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.amplificationMultiplier`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.countingArithmeticCutError`, `OAI.JointDickman.countingOriginParameter`, `OAI.JointDickman.squarefreeLeadingConstant`, `OAI.JointDickman.PublishedInputs.FiniteMcDiarmidInput`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.samplingTau` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.finite_graph_centered_mean_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingSamplingScale.lean (declaration OAI.JointDickman.counting_sampling_actual_scale)

import Mathlib
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

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

theorem counting_sampling_actual_scale_jd
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {L A : ℕ} {cap : ℝ} (hL : 10000 ≤ L) (hA : 0 < A) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ w ε : ℝ, 0 < w → 0 < ε →
      ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ Cmin Kerror : ℝ, 0 ≤ Cmin ∧ 0 ≤ Kerror ∧
      ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, Cmin ≤ C →
      ∀ J : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
        (∑ u ∈ range (J*N), countingArithmeticCutError P m B L (amplificationMultiplier B)
          (amplificationMultiplier B/A) (A*amplificationMultiplier B) τ C w c D
          (countingOriginParameter (amplificationMultiplier B) N u) u)/(N : ℝ) <
          (J : ℝ)*(ε+Kerror/(B : ℝ))+δ := by
  sorry

end JointDickman

end OAI
end
