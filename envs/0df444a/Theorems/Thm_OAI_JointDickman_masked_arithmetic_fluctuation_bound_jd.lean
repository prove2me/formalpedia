-- Prove2me | Theorems.Thm_OAI_JointDickman_masked_arithmetic_fluctuation_bound_jd
-- name    : OAI.JointDickman.masked_arithmetic_fluctuation_bound_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:28:09.387079+00:00
-- url     : https://prove2.me/theorems/43ff0544-0ca7-4d75-8166-eac19b602ec2
-- title:
--   OAI.JointDickman.masked_arithmetic_fluctuation_bound_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.masked_arithmetic_fluctuation_bound` of [lean/OAI/NumberTheory/JointDickman/Amplification/MaskedArithmeticFluctuation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/MaskedArithmeticFluctuation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter PublishedInputs Classical`, `open scoped Topology`):
--
--   ```lean
--   theorem masked_arithmetic_fluctuation_bound_jd
--       (hFord : FordUpperSieveInput) (hMertens : PrimeReciprocalMertensInput)
--       {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
--         0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M → M ≤ B^2 →
--         (M : ℝ) ≤ Real.exp B → ∀ χ : BlockCandidateIndex M → ℝ,
--         (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
--         arithmeticSquareMean B (fun u => maskedDigitCutError B L T H M τ C χ
--           (arithmeticFirstDigits B u)) ≤
--           K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+2/(B : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.BlockCandidateIndex`, `OAI.JointDickman.arithmeticFirstDigits`, `OAI.JointDickman.arithmeticSquareMean`, `OAI.JointDickman.conditionedRootError`, `OAI.JointDickman.maskedDigitCutError`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.samplingTau` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.finite_graph_arithmetic_fluctuation_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/MaskedArithmeticFluctuation.lean (declaration OAI.JointDickman.masked_arithmetic_fluctuation_bound)

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
open Finset Filter PublishedInputs Classical
open scoped Topology

theorem masked_arithmetic_fluctuation_bound_jd
    (hFord : FordUpperSieveInput) (hMertens : PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M → M ≤ B^2 →
      (M : ℝ) ≤ Real.exp B → ∀ χ : BlockCandidateIndex M → ℝ,
      (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      arithmeticSquareMean B (fun u => maskedDigitCutError B L T H M τ C χ
        (arithmeticFirstDigits B u)) ≤
        K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+2/(B : ℝ) := by
  sorry

end JointDickman

end OAI
end
