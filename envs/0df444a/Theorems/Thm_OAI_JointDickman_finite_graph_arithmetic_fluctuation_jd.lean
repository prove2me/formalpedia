-- Prove2me | Theorems.Thm_OAI_JointDickman_finite_graph_arithmetic_fluctuation_jd
-- name    : OAI.JointDickman.finite_graph_arithmetic_fluctuation_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:26:04.348203+00:00
-- url     : https://prove2.me/theorems/d282abd1-28a8-4f69-b4b4-211fd7919485
-- title:
--   OAI.JointDickman.finite_graph_arithmetic_fluctuation_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.finite_graph_arithmetic_fluctuation` of [lean/OAI/NumberTheory/JointDickman/Amplification/FiniteGraphFluctuation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/FiniteGraphFluctuation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter Classical`, `open scoped Topology`):
--
--   ```lean
--   theorem finite_graph_arithmetic_fluctuation_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
--       {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
--       ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
--         ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
--           0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
--           0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
--           ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ N : ℕ,
--             (∑ u ∈ range K, finiteGraphLatentError B L T H M N u τ C)/(K : ℝ) < E B+ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryCutoff`, `OAI.JointDickman.finiteGraphLatentError`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.samplingTau` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.finite_graph_centered_mean_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/FiniteGraphFluctuation.lean (declaration OAI.JointDickman.finite_graph_arithmetic_fluctuation)

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

theorem finite_graph_arithmetic_fluctuation_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
        0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ N : ℕ,
          (∑ u ∈ range K, finiteGraphLatentError B L T H M N u τ C)/(K : ℝ) < E B+ε := by
  sorry

end JointDickman

end OAI
end
