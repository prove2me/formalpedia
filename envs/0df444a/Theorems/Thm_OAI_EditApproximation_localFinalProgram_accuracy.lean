-- Prove2me | Theorems.Thm_OAI_EditApproximation_localFinalProgram_accuracy
-- name    : OAI.EditApproximation.localFinalProgram_accuracy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:37:11.404376+00:00
-- url     : https://prove2.me/theorems/2b06da45-cb11-40e1-9007-95e32a07389d
-- title:
--   OAI.EditApproximation.localFinalProgram_accuracy: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.localFinalProgram_accuracy` of [lean/OAI/Combinatorics/EditApproximation/Geometry/LocalFinalAccuracy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/LocalFinalAccuracy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem localFinalProgram_accuracy (incoming : Measure Seed) [IsProbabilityMeasure incoming]
--       (hinitial : incoming.real {seed | ¬ physicalSeedGood source target
--         ((integerParameters N).initialFactor : ℚ) seed} ≤ 1 / 100)
--       (rootQ : TargetInterval target.length) (epsilon : ℝ) (hepsilon : 0 < epsilon)
--       (haccuracy : 10 ≤ (inputSmallLog N : ℝ) * epsilon) :
--       (4 / 5 : ℝ) ≤ (localFinalProgramLaw (R := R) source target N P T S H incoming).real
--         {pair | stateEditCost source target rootQ ≤
--           localFinalProgramAnswer (R := R) source target N P T S H rootQ pair ∧
--           (localFinalProgramAnswer (R := R) source target N P T S H rootQ pair : ℝ) ≤
--             (1 + epsilon) * stateEditCost source target rootQ}
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.FiniteBernsteinInput` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.PhysicalLocalProgramKey` and `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.LocalFinalProgramDraw`, `OAI.EditApproximation.LocalFinalProgramOutcome` and `OAI.EditApproximation.PhysicalLocalProgramCoordinate` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalSeedGood` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.localFinalProgramAnswer`, `OAI.EditApproximation.localFinalProgramLaw` and `OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.smallLogExponent`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.intervalTreeDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.scheduledSeedFactor` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.groupDyadicScales` and `OAI.EditApproximation.groupSampleCount` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ClampedPhysicalSeed` and `OAI.EditApproximation.clampedSeedNat` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.groupDyadicScaleAt` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.local_physical_conditional_accuracy` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/LocalFinalAccuracy.lean (declaration OAI.EditApproximation.localFinalProgram_accuracy)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "terminalFactor" => scheduledSeedFactor N (computedSeedPassCount N)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

variable (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
  (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
  (hsize : source.length + target.length ≤ N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
theorem localFinalProgram_accuracy (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hinitial : incoming.real {seed | ¬ physicalSeedGood source target
      ((integerParameters N).initialFactor : ℚ) seed} ≤ 1 / 100)
    (rootQ : TargetInterval target.length) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (haccuracy : 10 ≤ (inputSmallLog N : ℝ) * epsilon) :
    (4 / 5 : ℝ) ≤ (localFinalProgramLaw (R := R) source target N P T S H incoming).real
      {pair | stateEditCost source target rootQ ≤
        localFinalProgramAnswer (R := R) source target N P T S H rootQ pair ∧
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ pair : ℝ) ≤
          (1 + epsilon) * stateEditCost source target rootQ} := by
  sorry

end Final

end EditApproximation

end OAI
end
