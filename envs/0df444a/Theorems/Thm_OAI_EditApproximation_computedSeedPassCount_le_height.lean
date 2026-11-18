-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedSeedPassCount_le_height
-- name    : OAI.EditApproximation.computedSeedPassCount_le_height
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:21:53.420048+00:00
-- url     : https://prove2.me/theorems/1e94ed56-2ba0-40d3-9813-14ea01c8bc7f
-- title:
--   OAI.EditApproximation.computedSeedPassCount_le_height: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedSeedPassCount_le_height` of [lean/OAI/Combinatorics/EditApproximation/Geometry/SeedFactorSchedule.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/SeedFactorSchedule.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem computedSeedPassCount_le_height (N : ℕ) (hN : 0 < N)
--       (hell : 2 ^ 1000 ≤ inputSmallLog N) : computedSeedPassCount N ≤ inputHeight N
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight` and `OAI.EditApproximation.inputSmallLog` (the published bundle `Def_EditApproxScheme_01`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedFamilyMemoCode_fits`, `OAI.EditApproximation.computedQuerySetupWithWork_cost`, `OAI.EditApproximation.computedQueryTable_work_width`, `OAI.EditApproximation.computed_physicalFamilyCode_bound` and `OAI.EditApproximation.localFinalProgram_accuracy` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/SeedFactorSchedule.lean (declaration OAI.EditApproximation.computedSeedPassCount_le_height)

import Mathlib
import Definitions.Def_EditApproxScheme_01

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem computedSeedPassCount_le_height (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) : computedSeedPassCount N ≤ inputHeight N := by
  sorry

end EditApproximation

end OAI
end
