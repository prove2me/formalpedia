-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedFamilyMemoCode_fits
-- name    : OAI.EditApproximation.computedFamilyMemoCode_fits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:21:53.326629+00:00
-- url     : https://prove2.me/theorems/8c5e9c0c-ae31-44bb-9fdb-51b583f7b763
-- title:
--   OAI.EditApproximation.computedFamilyMemoCode_fits: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedFamilyMemoCode_fits` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedFamilyMemoCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedFamilyMemoCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--    theorem computedFamilyMemoCode_fits (source target : List ℕ) (N R : ℕ)
--       (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
--       (hR : R ≤ inputHeight N ^ 2)
--       (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
--         (inputHeight N)) ≤ inputHeight N)
--       (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
--       computedFamilyMemoCode source target N R key < 2 ^ (16384 * inputHeight N + 5)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.localOnlineMassBound` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.ComputedFamilyTableKey` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ComputedFamilyScalarKey` and `OAI.EditApproximation.computedFamilyMemoCode` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedFamilyResult_requests_le`, `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le`, `OAI.EditApproximation.computedQueryMemoResult_storage`, `OAI.EditApproximation.computedQueryTemporaryCells_polynomial` and `OAI.EditApproximation.integerBinaryOutput_cost` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedFamilyMemoCode.lean (declaration OAI.EditApproximation.computedFamilyMemoCode_fits)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Geometric
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_14

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computedFamilyMemoCode_fits (source target : List ℕ) (N R : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    computedFamilyMemoCode source target N R key < 2 ^ (16384 * inputHeight N + 5) := by
  sorry

end EditApproximation

end OAI
end
