-- Prove2me | Theorems.Thm_OAI_JointDickman_finite_ramp_approximation_jd
-- name    : OAI.JointDickman.finite_ramp_approximation_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:27:04.306279+00:00
-- url     : https://prove2.me/theorems/2cabc79d-08b6-4b0d-ac5e-1291eb48913a
-- title:
--   OAI.JointDickman.finite_ramp_approximation_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.finite_ramp_approximation` of [lean/OAI/NumberTheory/JointDickman/Amplification/FiniteRampApproximation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/FiniteRampApproximation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter Classical`, `open scoped Topology`):
--
--   ```lean
--   theorem finite_ramp_approximation_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
--       {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
--       ∃ A : ℝ, 0 < A ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C δ : ℝ),
--         0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M → M ≤ B^2 → 0 < δ →
--         ∀ (J : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, K ≤ J*N →
--           (∑ u ∈ range K, finiteRampCutError B L T H M N u τ C δ)/(N : ℝ) <
--             A*(T : ℝ)*δ+ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.finiteRampCutError`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.samplingTau` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.finite_graph_centered_mean_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/FiniteRampApproximation.lean (declaration OAI.JointDickman.finite_ramp_approximation)

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
open Finset Filter Classical
open scoped Topology

theorem finite_ramp_approximation_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C δ : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M → M ≤ B^2 → 0 < δ →
      ∀ (J : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, K ≤ J*N →
        (∑ u ∈ range K, finiteRampCutError B L T H M N u τ C δ)/(N : ℝ) <
          A*(T : ℝ)*δ+ε := by
  sorry

end JointDickman

end OAI
end
