-- Prove2me | Theorems.Thm_OAI_EditApproximation_integerBinaryAnswer_conditional_accuracy
-- name    : OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:36:52.600038+00:00
-- url     : https://prove2.me/theorems/4ba72519-53a2-4f29-a240-95e2ce8f8697
-- title:
--   OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy` of [lean/OAI/Combinatorics/EditApproximation/Binary/IntegerBinaryAccuracy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/IntegerBinaryAccuracy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open MeasureTheory`):
--
--   ```lean
--   theorem integerBinaryAnswer_conditional_accuracy (source target : List ℤ) (N : ℕ)
--       (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
--       (hsize : source.length + target.length ≤ N) (bernstein : ComputedBernsteinInputs N) :
--       (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
--         {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
--           (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
--             (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.ComputedBernsteinInputs` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.integerBinaryAnswer` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.integerSymbolCode`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.CoarseThresholdDraws`, `OAI.EditApproximation.PhysicalNode` and `OAI.EditApproximation.intervalTreeDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.substring` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` and `OAI.EditApproximation.physicalSource` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.coarseDrawsMeasurableSpace` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.CoarseGuessIndex` and `OAI.EditApproximation.coarseEntryWidth` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditDistortion.edit` (the published bundle `Def_EditApproxScheme_12`); `OAI.EditApproximation.computedPhysicalCoarseDepth` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.ComputedExecutionOutcome`, `OAI.EditApproximation.ComputedFullOutcome`, `OAI.EditApproximation.ComputedPhysicalCoarseDraw`, `OAI.EditApproximation.ComputedRejectionRuntime`, `OAI.EditApproximation.computedFullLaw` and `OAI.EditApproximation.physicalFamilyRange` (the published bundle `Def_EditApproxScheme_16`).
--
--   **Used by.** The proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/IntegerBinaryAccuracy.lean (declaration OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open MeasureTheory

theorem integerBinaryAnswer_conditional_accuracy (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (hsize : source.length + target.length ≤ N) (bernstein : ComputedBernsteinInputs N) :
    (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
      {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
        (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  sorry

end EditApproximation

end OAI
end
