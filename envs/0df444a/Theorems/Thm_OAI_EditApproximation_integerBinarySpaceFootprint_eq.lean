-- Prove2me | Theorems.Thm_OAI_EditApproximation_integerBinarySpaceFootprint_eq
-- name    : OAI.EditApproximation.integerBinarySpaceFootprint_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:36:52.623283+00:00
-- url     : https://prove2.me/theorems/6af59ad8-8d1d-4b58-9dd3-2c0757ca3577
-- title:
--   OAI.EditApproximation.integerBinarySpaceFootprint_eq: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.integerBinarySpaceFootprint_eq` of [lean/OAI/Combinatorics/EditApproximation/Specification/FootprintMain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Specification/FootprintMain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter MeasureTheory`):
--
--   ```lean
--   theorem integerBinarySpaceFootprint_eq (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
--       (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
--       integerBinarySpaceFootprint source target N epsilon outcome =
--         integerBinarySpace source target N epsilon outcome
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.integerBinarySpace` and `OAI.EditApproximation.integerBinarySpaceFootprint` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.integerSymbolCode` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.ComputedFullOutcome` (the published bundle `Def_EditApproxScheme_16`).
--
--   **Used by.** The proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Specification/FootprintMain.lean (declaration OAI.EditApproximation.integerBinarySpaceFootprint_eq)

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
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero

theorem integerBinarySpaceFootprint_eq (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinarySpaceFootprint source target N epsilon outcome =
      integerBinarySpace source target N epsilon outcome := by
  sorry

end OAI.EditApproximation
end
