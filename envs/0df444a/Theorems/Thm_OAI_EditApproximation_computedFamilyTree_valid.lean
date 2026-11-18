-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedFamilyTree_valid
-- name    : OAI.EditApproximation.computedFamilyTree_valid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:23.515205+00:00
-- url     : https://prove2.me/theorems/7d037753-181a-4d3b-9d31-2cba47a3d3b5
-- title:
--   OAI.EditApproximation.computedFamilyTree_valid: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedFamilyTree_valid` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter MeasureTheory`):
--
--   ```lean
--    theorem computedFamilyTree_valid (source target : List ℕ) (N : ℕ)
--       (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (input : ComputedFamilyInput source target N) :
--       (computedFamilyTree source target N input).Valid
--         ((integerParameters N).M * inputSmallLog N ^ 257)
--         (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedFamilyTree` and `OAI.EditApproximation.DependencyExpansion.Valid` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.coarseExponent`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.ComputedFamilyInput` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedFamilyCoarseInputWork_le` and `OAI.EditApproximation.computedFamilyResult_requests_le` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalWork.lean (declaration OAI.EditApproximation.computedFamilyTree_valid)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Filter MeasureTheory

 theorem computedFamilyTree_valid (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (input : ComputedFamilyInput source target N) :
    (computedFamilyTree source target N input).Valid
      ((integerParameters N).M * inputSmallLog N ^ 257)
      (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) := by
  sorry

end EditApproximation

end OAI
end
