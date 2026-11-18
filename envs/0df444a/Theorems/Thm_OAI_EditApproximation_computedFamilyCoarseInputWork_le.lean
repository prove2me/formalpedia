-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedFamilyCoarseInputWork_le
-- name    : OAI.EditApproximation.computedFamilyCoarseInputWork_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:45.590221+00:00
-- url     : https://prove2.me/theorems/e24f006e-03e5-439d-b917-b67690dcca18
-- title:
--   OAI.EditApproximation.computedFamilyCoarseInputWork_le: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedFamilyCoarseInputWork_le` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseInputWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseInputWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter MeasureTheory`):
--
--   ```lean
--   theorem computedFamilyCoarseInputWork_le (source target : List ℕ) (N : ℕ)
--       (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
--       (hsize : source.length + target.length ≤ N)
--       (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
--         (inputHeight N)) ≤ inputHeight N)
--       (input : ComputedFamilyInput source target N) :
--       computedFamilyCoarseInputWork source target N input ≤ computedWidthEnvelope N
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedWidthEnvelope` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.computedFamilyCoarseInputWork` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.localOnlineMassBound` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.ComputedFamilyInput` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedExecutionIndexedCoarseWork_expected_near_linear` and `OAI.EditApproximation.computedExecutionTotalWork_expected_near_linear` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseInputWork.lean (declaration OAI.EditApproximation.computedFamilyCoarseInputWork_le)

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
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

theorem computedFamilyCoarseInputWork_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
    (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseInputWork source target N input ≤ computedWidthEnvelope N := by
  sorry

end EditApproximation

end OAI
end
