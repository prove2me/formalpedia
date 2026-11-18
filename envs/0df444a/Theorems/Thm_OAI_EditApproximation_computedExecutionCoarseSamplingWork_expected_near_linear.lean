-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedExecutionCoarseSamplingWork_expected_near_linear
-- name    : OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:20:43.774351+00:00
-- url     : https://prove2.me/theorems/61c68f23-14f4-4021-9c44-7ff33b1d3d5e
-- title:
--   OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseSamplingWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseSamplingWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open MeasureTheory Filter`):
--
--   ```lean
--   theorem computedExecutionCoarseSamplingWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
--       ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
--         (∫ execution, computedExecutionCoarseSamplingWork source target N execution
--           ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.CoarseThresholdDraws`, `OAI.EditApproximation.PhysicalNode` and `OAI.EditApproximation.intervalTreeDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.substring` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` and `OAI.EditApproximation.physicalSource` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.coarseDrawsMeasurableSpace` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.CoarseGuessIndex` and `OAI.EditApproximation.coarseEntryWidth` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.computedPhysicalCoarseDepth` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.ComputedExecutionOutcome`, `OAI.EditApproximation.ComputedPhysicalCoarseDraw`, `OAI.EditApproximation.ComputedRejectionRuntime`, `OAI.EditApproximation.computedExecutionCoarseSamplingWork`, `OAI.EditApproximation.computedExecutionLaw` and `OAI.EditApproximation.physicalFamilyRange` (the published bundle `Def_EditApproxScheme_16`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedExecutionTotalWork_expected_near_linear` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedCoarseSamplingWork.lean (declaration OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear)

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
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_16

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open MeasureTheory Filter

theorem computedExecutionCoarseSamplingWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionCoarseSamplingWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  sorry

end EditApproximation

end OAI
end
