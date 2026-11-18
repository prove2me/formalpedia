-- Prove2me | Theorems.Thm_OAI_EditApproximation_computed_physicalFamilyCode_bound
-- name    : OAI.EditApproximation.computed_physicalFamilyCode_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:21:53.608675+00:00
-- url     : https://prove2.me/theorems/7da7556c-bf03-40df-97b8-964f79d22536
-- title:
--   OAI.EditApproximation.computed_physicalFamilyCode_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computed_physicalFamilyCode_bound` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedFamilyEncoding.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedFamilyEncoding.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--    theorem computed_physicalFamilyCode_bound (N nx ny R : ℕ)
--       (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
--       (hR : R ≤ inputHeight N ^ 2)
--       (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
--         (inputHeight N)) ≤ inputHeight N)
--       (target : List ℕ) (htarget : target.length = ny)
--       (key : PhysicalFamilyScalarKey (M := (integerParameters N).M)
--         (J := intervalTreeDepth (integerParameters N).M nx) (R := R)
--         target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
--         (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)) :
--       physicalFamilyCode target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
--         (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2) key <
--         2 ^ (16384 * inputHeight N + 4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.intervalTreeDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.localOnlineMassBound` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.PhysicalFamilyScalarKey` and `OAI.EditApproximation.physicalFamilyCode` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedFamilyMemoCode_fits` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedFamilyEncoding.lean (declaration OAI.EditApproximation.computed_physicalFamilyCode_bound)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Geometric
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_14

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_physicalFamilyCode_bound (N nx ny R : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (target : List ℕ) (htarget : target.length = ny)
    (key : PhysicalFamilyScalarKey (M := (integerParameters N).M)
      (J := intervalTreeDepth (integerParameters N).M nx) (R := R)
      target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
      (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)) :
    physicalFamilyCode target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
      (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2) key <
      2 ^ (16384 * inputHeight N + 4) := by
  sorry

end EditApproximation

end OAI
end
