-- Prove2me | Theorems.Thm_OAI_EditApproximation_weighted_dependency_div_height_tendsto
-- name    : OAI.EditApproximation.weighted_dependency_div_height_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:31:11.07301+00:00
-- url     : https://prove2.me/theorems/99ea1429-e5f4-4094-ae09-f37abf7f7efe
-- title:
--   OAI.EditApproximation.weighted_dependency_div_height_tendsto: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.weighted_dependency_div_height_tendsto` of [lean/OAI/Combinatorics/EditApproximation/Geometry/ParameterDependencyAsymptotics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/ParameterDependencyAsymptotics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem weighted_dependency_div_height_tendsto :
--       Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
--         computedDependencyIndexCount N * Real.log (inputHeight N : ℝ) / inputHeight N)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedDependencyIndexCount` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.coarseExponent`, `OAI.EditApproximation.inputHeight` and `OAI.EditApproximation.inputSmallLog` (the published bundle `Def_EditApproxScheme_01`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear`, `OAI.EditApproximation.computedExecutionIndexedCoarseWork_expected_near_linear`, `OAI.EditApproximation.computedExecutionNonlocalWork_expected_near_linear`, `OAI.EditApproximation.computedExecutionTotalWork_expected_near_linear`, `OAI.EditApproximation.computedQueryTemporaryCells_polynomial` and `OAI.EditApproximation.integerBinarySpace_polynomial` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/ParameterDependencyAsymptotics.lean (declaration OAI.EditApproximation.weighted_dependency_div_height_tendsto)

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

open Filter
open scoped Topology

theorem weighted_dependency_div_height_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
      computedDependencyIndexCount N * Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) := by
  sorry

end EditApproximation

end OAI
end
