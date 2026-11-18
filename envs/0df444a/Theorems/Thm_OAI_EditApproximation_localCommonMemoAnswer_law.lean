-- Prove2me | Theorems.Thm_OAI_EditApproximation_localCommonMemoAnswer_law
-- name    : OAI.EditApproximation.localCommonMemoAnswer_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:28.931695+00:00
-- url     : https://prove2.me/theorems/4cbb4ffa-d6a3-474a-af09-3dbcb518ea56
-- title:
--   OAI.EditApproximation.localCommonMemoAnswer_law: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.localCommonMemoAnswer_law` of [lean/OAI/Combinatorics/EditApproximation/Geometry/LocalCommonOutput.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/LocalCommonOutput.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem localCommonMemoAnswer_law (hP : 0 < P) (hH : 0 < H)
--       (incoming : Measure Seed) [IsProbabilityMeasure incoming]
--       (rootQ : TargetInterval target.length) :
--       (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming).map
--           (localCommonMemoAnswer source target N P T S H hP hH rootQ) =
--         (localFinalProgramLaw (R := R) source target N P T S H incoming).map
--           (localFinalProgramAnswer (R := R) source target N P T S H rootQ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalLocalProgramKey` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.LocalCommonDraw`, `OAI.EditApproximation.LocalCommonFinalOutcome`, `OAI.EditApproximation.LocalCommonTerminalDraw`, `OAI.EditApproximation.LocalCommonTrace`, `OAI.EditApproximation.LocalFinalProgramDraw`, `OAI.EditApproximation.LocalFinalProgramOutcome`, `OAI.EditApproximation.PhysicalCommonCoordinate`, `OAI.EditApproximation.PhysicalCommonDraw`, `OAI.EditApproximation.PhysicalLocalProgramCoordinate` and `OAI.EditApproximation.commonSeedTraceMeasurable` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.localCommonFinalLaw`, `OAI.EditApproximation.localCommonMemoAnswer`, `OAI.EditApproximation.localFinalProgramAnswer`, `OAI.EditApproximation.localFinalProgramLaw`, `OAI.EditApproximation.physicalCommonCoordinateMeasurable` and `OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.localOnlineMassBound` and `OAI.EditApproximation.scheduledSeedFactor` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ClampedPhysicalSeed`, `OAI.EditApproximation.PhysicalCommonKey` and `OAI.EditApproximation.clampedSeedNat` (the published bundle `Def_EditApproxScheme_10`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalFamilyFinalAnswer_law` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/LocalCommonOutput.lean (declaration OAI.EditApproximation.localCommonMemoAnswer_law)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "passes" => computedSeedPassCount N

theorem localCommonMemoAnswer_law (hP : 0 < P) (hH : 0 < H)
    (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (rootQ : TargetInterval target.length) :
    (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming).map
        (localCommonMemoAnswer source target N P T S H hP hH rootQ) =
      (localFinalProgramLaw (R := R) source target N P T S H incoming).map
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ) := by
  sorry

end Output

end EditApproximation

end OAI
end
