-- Prove2me | Theorems.Thm_OAI_JointDickman_nonzero_binLabel_correlation_along_forces_energy_jd
-- name    : OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:29:02.231222+00:00
-- url     : https://prove2.me/theorems/3de82720-c804-4327-b7d7-07e238f4637e
-- title:
--   OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy` of [lean/OAI/NumberTheory/JointDickman/Counting/SubsequencePositiveEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/SubsequencePositiveEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem nonzero_binLabel_correlation_along_forces_energy_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput)
--       {ι : Type*} [Fintype ι]
--       (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
--       (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
--       (H : ℕ → ℕ → ℂ) (hH : ∀ N n, ‖H N n‖ ≤ 2)
--       (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ} (hβ : β ≠ 0)
--       (hmean : Tendsto (fun N => (∑ n ∈ range (r N),
--         star (movingBinLabel J k z (r N) n) * H (r N) n)/(r N : ℂ)) atTop (nhds β)) :
--       ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ e : ℝ, 0 < e ∧
--         ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
--           ∀ C : ℝ, C₀ ≤ C → ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
--             e ≤ firstFormEnergy B L τ C (amplificationOuterWeight B)
--               (amplificationInnerWeight (amplificationMultiplier B)) (H (r (s N))) (r (s N)) /
--                 ((B : ℝ)*amplificationMultiplier B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.amplificationInnerWeight`, `OAI.JointDickman.amplificationMultiplier`, `OAI.JointDickman.amplificationOuterWeight`, `OAI.JointDickman.firstFormEnergy`, `OAI.JointDickman.movingBinLabel`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.rationalFixedScaleLaw_of_distance_divergence_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/SubsequencePositiveEnergy.lean (declaration OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy)

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

theorem nonzero_binLabel_correlation_along_forces_energy_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (H : ℕ → ℕ → ℂ) (hH : ∀ N n, ‖H N n‖ ≤ 2)
    (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ} (hβ : β ≠ 0)
    (hmean : Tendsto (fun N => (∑ n ∈ range (r N),
      star (movingBinLabel J k z (r N) n) * H (r N) n)/(r N : ℂ)) atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ e : ℝ, 0 < e ∧
      ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
        ∀ C : ℝ, C₀ ≤ C → ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
          e ≤ firstFormEnergy B L τ C (amplificationOuterWeight B)
            (amplificationInnerWeight (amplificationMultiplier B)) (H (r (s N))) (r (s N)) /
              ((B : ℝ)*amplificationMultiplier B) := by
  sorry

end JointDickman

end OAI
end
