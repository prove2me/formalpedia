-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalFamilyFinalAnswer_law
-- name    : OAI.EditApproximation.physicalFamilyFinalAnswer_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:33.193195+00:00
-- url     : https://prove2.me/theorems/60afb02a-722c-4a2e-9b93-10b0227ecdcb
-- title:
--   OAI.EditApproximation.physicalFamilyFinalAnswer_law: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalFamilyFinalAnswer_law` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyOutput.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyOutput.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open MeasureTheory ProbabilityTheory`):
--
--   ```lean
--    theorem physicalFamilyFinalAnswer_law (hH : 0 < H) (incoming : Measure SeedState)
--       [IsProbabilityMeasure incoming] (rootQ : TargetInterval target.length) :
--       (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
--         target N P ell exponent H (ell ^ 80) passes (H ^ 2))).map
--           (physicalFamilyFinalAnswer source target N P T S H hP rootQ) =
--       (localFinalProgramLaw (R := R) source target N P T S H incoming).map
--           (localFinalProgramAnswer (R := R) source target N P T S H rootQ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalLocalProgramKey` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.LocalFinalProgramDraw`, `OAI.EditApproximation.LocalFinalProgramOutcome` and `OAI.EditApproximation.PhysicalLocalProgramCoordinate` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalFamilyLaw` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.localFinalProgramAnswer`, `OAI.EditApproximation.localFinalProgramLaw`, `OAI.EditApproximation.physicalFamilyFinalAnswer` and `OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.localOnlineMassBound` and `OAI.EditApproximation.scheduledSeedFactor` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ClampedPhysicalSeed` and `OAI.EditApproximation.clampedSeedNat` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.PhysicalScalarKey` and `OAI.EditApproximation.physicalScalarRange` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.PhysicalFamilyScalarDraw` and `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalFamilyRuntimeAnswer_event` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyOutput.lean (declaration OAI.EditApproximation.physicalFamilyFinalAnswer_law)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Geometric
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ) (hP : 0 < P)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N

 theorem physicalFamilyFinalAnswer_law (hH : 0 < H) (incoming : Measure SeedState)
    [IsProbabilityMeasure incoming] (rootQ : TargetInterval target.length) :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).map
        (physicalFamilyFinalAnswer source target N P T S H hP rootQ) =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).map
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ) := by
  sorry

end Output

end EditApproximation

end OAI
end
