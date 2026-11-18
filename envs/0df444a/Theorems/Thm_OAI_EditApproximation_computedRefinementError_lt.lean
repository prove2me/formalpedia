-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedRefinementError_lt
-- name    : OAI.EditApproximation.computedRefinementError_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:15.035195+00:00
-- url     : https://prove2.me/theorems/8c53ce3a-97f8-41bc-8093-077cefafa95f
-- title:
--   OAI.EditApproximation.computedRefinementError_lt: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedRefinementError_lt` of [lean/OAI/Combinatorics/EditApproximation/Geometry/RefinementErrorTerms.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/RefinementErrorTerms.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem computedRefinementError_lt (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
--       (hell : 2 ^ 1000 ≤ inputSmallLog N) : computedRefinementError N nx < 1 / (inputSmallLog N : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedRefinementError` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.inputSmallLog` (the published bundle `Def_EditApproxScheme_01`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.physicalProgram_expected_root_excess` and `OAI.EditApproximation.physicalProgram_expected_state_excess` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/RefinementErrorTerms.lean (declaration OAI.EditApproximation.computedRefinementError_lt)

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_OAIQ361V3Ea001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem computedRefinementError_lt (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) : computedRefinementError N nx < 1 / (inputSmallLog N : ℝ) := by
  sorry

end EditApproximation

end OAI
end
