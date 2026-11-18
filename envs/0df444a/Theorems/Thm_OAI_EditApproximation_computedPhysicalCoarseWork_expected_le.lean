-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedPhysicalCoarseWork_expected_le
-- name    : OAI.EditApproximation.computedPhysicalCoarseWork_expected_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:50.460002+00:00
-- url     : https://prove2.me/theorems/7cfb9ecb-a2ed-4a5d-ae81-dac8c788d5a2
-- title:
--   OAI.EditApproximation.computedPhysicalCoarseWork_expected_le: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalCoarseWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalCoarseWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open MeasureTheory Filter`):
--
--   ```lean
--    theorem computedPhysicalCoarseWork_expected_le (source target : List ℕ) (N : ℕ)
--       (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
--       (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
--         (inputHeight N)) ≤ inputHeight N)
--       (hinverse : coarseInverseAllowanceFactor (integerParameters N).B
--         (initialThresholdQ N) (initialLambda N) ≤ (inputHeight N : ℝ) ^ 8) :
--       ComputedPhysicalCoarseBudget source target N
--         (computedWidthEnvelope N * computedCoarseWidthOverhead N)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.coarseInverseAllowanceFactor`, `OAI.EditApproximation.computedCoarseWidthOverhead` and `OAI.EditApproximation.computedWidthEnvelope` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.ComputedPhysicalCoarseBudget` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.initialLambda`, `OAI.EditApproximation.initialThresholdQ`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.localOnlineMassBound` (the published bundle `Def_EditApproxScheme_03`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear`, `OAI.EditApproximation.computedExecutionIndexedCoarseWork_expected_near_linear` and `OAI.EditApproximation.computedExecutionNonlocalWork_expected_near_linear` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedPhysicalCoarseWork.lean (declaration OAI.EditApproximation.computedPhysicalCoarseWork_expected_le)

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
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory Filter

 theorem computedPhysicalCoarseWork_expected_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hinverse : coarseInverseAllowanceFactor (integerParameters N).B
      (initialThresholdQ N) (initialLambda N) ≤ (inputHeight N : ℝ) ^ 8) :
    ComputedPhysicalCoarseBudget source target N
      (computedWidthEnvelope N * computedCoarseWidthOverhead N) := by
  sorry

end EditApproximation

end OAI
end
