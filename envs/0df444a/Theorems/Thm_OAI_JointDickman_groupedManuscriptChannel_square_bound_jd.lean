-- Prove2me | Theorems.Thm_OAI_JointDickman_groupedManuscriptChannel_square_bound_jd
-- name    : OAI.JointDickman.groupedManuscriptChannel_square_bound_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:28:54.585373+00:00
-- url     : https://prove2.me/theorems/2ba61264-3131-41e9-8908-18373c11861e
-- title:
--   OAI.JointDickman.groupedManuscriptChannel_square_bound_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.groupedManuscriptChannel_square_bound` of [lean/OAI/NumberTheory/JointDickman/Arithmetic/LogarithmicMarginal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/LogarithmicMarginal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`):
--
--   ```lean
--   theorem groupedManuscriptChannel_square_bound_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput) :
--       ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in Filter.atTop,
--         ∀ g : (auxiliaryPrimes B → Bool) → ℝ,
--         (∑ a : Fin m × Fin (channelBlockCount m B), channelMesh (channelFineCount m B)*
--           groupedManuscriptChannel m B g a^2) ≤
--           C*∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.channelBlockCount`, `OAI.JointDickman.channelFineCount`, `OAI.JointDickman.channelMesh`, `OAI.JointDickman.fullPrimeMass`, `OAI.JointDickman.groupedManuscriptChannel`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.bounded_box_coarse_comparison_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/LogarithmicMarginal.lean (declaration OAI.JointDickman.groupedManuscriptChannel_square_bound)

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

theorem groupedManuscriptChannel_square_bound_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in Filter.atTop,
      ∀ g : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin m × Fin (channelBlockCount m B), channelMesh (channelFineCount m B)*
        groupedManuscriptChannel m B g a^2) ≤
        C*∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2 := by
  sorry

end JointDickman

end OAI
end
