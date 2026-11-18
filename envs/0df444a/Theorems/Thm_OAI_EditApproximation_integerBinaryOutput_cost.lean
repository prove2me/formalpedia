-- Prove2me | Theorems.Thm_OAI_EditApproximation_integerBinaryOutput_cost
-- name    : OAI.EditApproximation.integerBinaryOutput_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:24:06.128326+00:00
-- url     : https://prove2.me/theorems/a9c418c1-5457-4d9f-a492-f45a3bb6cde6
-- title:
--   OAI.EditApproximation.integerBinaryOutput_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.integerBinaryOutput_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/IntegerBinaryOutput.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/IntegerBinaryOutput.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem integerBinaryOutput_cost (source target : List ℤ) (N : ℕ)
--       (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
--       (hsize : source.length + target.length ≤ N)
--       (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
--       (integerBinaryOutput source target N input).2 ≤ N + inputHeight N ^ 10
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.integerBinaryOutput` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.inputHeight` and `OAI.EditApproximation.integerSymbolCode` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.ComputedFamilyInput` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.physicalLargeInput` (the published bundle `Def_EditApproxScheme_16`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.integerBinarySpace_polynomial` and `OAI.EditApproximation.integerBinaryWork_expected_near_linear` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/IntegerBinaryOutput.lean (declaration OAI.EditApproximation.integerBinaryOutput_cost)

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
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem integerBinaryOutput_cost (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
    (hsize : source.length + target.length ≤ N)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    (integerBinaryOutput source target N input).2 ≤ N + inputHeight N ^ 10 := by
  sorry

end EditApproximation

end OAI
end
