-- Prove2me | Theorems.Thm_OAI_JointDickman_amplification_positive_mass_bound_jd
-- name    : OAI.JointDickman.amplification_positive_mass_bound_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:21:41.473218+00:00
-- url     : https://prove2.me/theorems/0b186c5a-f58b-4a53-9a8e-b7159b9ec8fd
-- title:
--   OAI.JointDickman.amplification_positive_mass_bound_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.amplification_positive_mass_bound` of [lean/OAI/NumberTheory/JointDickman/Amplification/AmplificationPositiveMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/AmplificationPositiveMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem amplification_positive_mass_bound_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput)
--       {η : ℝ} (hη : 0 < η) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
--         ∀ᶠ B : ℕ in atTop, ∀ j : ℕ, [NeZero j] →
--           ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
--           ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
--           ∀ U V : ℕ,
--             (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
--               ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
--             (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
--               ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
--             T*amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) ≤
--               ε B+K*(T/j)*singularSeries j
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.amplificationArithmeticSum`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.dyadicBoxIndices`, `OAI.JointDickman.dyadicBoxLower`, `OAI.JointDickman.dyadicBoxUpper`, `OAI.JointDickman.singularSeries`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.counting_block_test_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/AmplificationPositiveMass.lean (declaration OAI.JointDickman.amplification_positive_mass_bound)

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

theorem amplification_positive_mass_bound_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ j : ℕ, [NeZero j] →
        ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
        ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
        ∀ U V : ℕ,
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          T*amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) ≤
            ε B+K*(T/j)*singularSeries j := by
  sorry

end JointDickman

end OAI
end
