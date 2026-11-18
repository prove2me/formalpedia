-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedQueryMemoResult_decode
-- name    : OAI.EditApproximation.computedQueryMemoResult_decode
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:04.256204+00:00
-- url     : https://prove2.me/theorems/dbc003b9-545d-4ccc-bfb1-2083ed9a943d
-- title:
--   OAI.EditApproximation.computedQueryMemoResult_decode: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedQueryMemoResult_decode` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryExecution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryExecution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem computedQueryMemoResult_decode :
--       (computedQueryMemoResult source target N occurrence symbolBits positionBits input).decode =
--         computedFamilyResult source target N input
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BitRecursiveMemoResult.decode` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.computedQueryMemoResult` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryMemo`, `OAI.EditApproximation.PositionCounts`, `OAI.EditApproximation.RecursiveMemoResult`, `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.intervalTreeDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.localOnlineMassBound` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.ChargedPhysicalRequest` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.occurrenceBuild` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.ComputedFamilyInput` and `OAI.EditApproximation.ComputedFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.computedFamilyResult` (the published bundle `Def_EditApproxScheme_16`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedQueryAnswerWithWork_value`, `OAI.EditApproximation.computedQueryTemporaryCells_polynomial` and `OAI.EditApproximation.integerBinarySpace_polynomial` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryExecution.lean (declaration OAI.EditApproximation.computedQueryMemoResult_decode)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

section Correct
variable (source target : List ℕ) (N : ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (input : ComputedFamilyInput source target N) (hN : 0 < N)
  (hell : 2 ^ 1000 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
  (hsize : source.length + target.length ≤ N)
  (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
    (inputHeight N)) ≤ inputHeight N)
  (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
  (hp : target.length ≤ 2 ^ positionBits)
  (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)

include hN hell hf hsize hMass hs ht hp htable in
theorem computedQueryMemoResult_decode :
    (computedQueryMemoResult source target N occurrence symbolBits positionBits input).decode =
      computedFamilyResult source target N input := by
  sorry

end Correct
end EditApproximation

end OAI
end
