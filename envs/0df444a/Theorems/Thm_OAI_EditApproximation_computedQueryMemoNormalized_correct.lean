-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedQueryMemoNormalized_correct
-- name    : OAI.EditApproximation.computedQueryMemoNormalized_correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:38.523208+00:00
-- url     : https://prove2.me/theorems/813cb0cd-8aa8-46a6-a095-f1293af9df8a
-- title:
--   OAI.EditApproximation.computedQueryMemoNormalized_correct: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedQueryMemoNormalized_correct` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem computedQueryMemoNormalized_correct (source target : List ℕ) (N : ℕ)
--       (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
--       (input : ComputedFamilyInput source target N) (hf : 3 ≤ smallLogExponent N)
--       (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
--       (hp : target.length ≤ 2 ^ positionBits)
--       (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
--       (key : ComputedFamilyMemoKey source target N) :
--       (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
--         (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) key).value =
--           computedFamilyExpectedValue source target N input key ∧
--       BitQuery.RefinesOn
--         (fun child => rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
--           (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) child.val)
--         (fun word value => word.value = value)
--         (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key)
--         (computedQueryReference source target N input key)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BitQuery.RefinesOn` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.computedFamilyExpectedValue`, `OAI.EditApproximation.computedQueryMemoNormalized` and `OAI.EditApproximation.computedQueryReference` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo`, `OAI.EditApproximation.PositionCounts`, `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.intervalTreeDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.rankedBitProgramValue` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.occurrenceBuild` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` and `OAI.EditApproximation.SourceRanked.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.ComputedFamilyInput`, `OAI.EditApproximation.ComputedFamilyMemoKey` and `OAI.EditApproximation.ComputedFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedQueryMemoResult_decode`, `OAI.EditApproximation.computedQueryTemporaryCells_polynomial` and `OAI.EditApproximation.integerBinaryWork_expected_near_linear` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryCorrect.lean (declaration OAI.EditApproximation.computedQueryMemoNormalized_correct)

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
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
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

attribute [local instance] queryArityNeZero queryRoundsNeZero

theorem computedQueryMemoNormalized_correct (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hf : 3 ≤ smallLogExponent N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (key : ComputedFamilyMemoKey source target N) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
      (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) key).value =
        computedFamilyExpectedValue source target N input key ∧
    BitQuery.RefinesOn
      (fun child => rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
        (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) child.val)
      (fun word value => word.value = value)
      (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key)
      (computedQueryReference source target N input key) := by
  sorry

end EditApproximation

end OAI
end
