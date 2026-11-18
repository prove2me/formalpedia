-- Prove2me | Theorems.Thm_OAI_EditApproximation_localScheduledSeedNext_event
-- name    : OAI.EditApproximation.localScheduledSeedNext_event
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:51.415874+00:00
-- url     : https://prove2.me/theorems/3ca31e03-d5fe-48c5-8af6-8b2784543902
-- title:
--   OAI.EditApproximation.localScheduledSeedNext_event: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.localScheduledSeedNext_event` of [lean/OAI/Combinatorics/EditApproximation/Geometry/LocalSeedSchedule.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/LocalSeedSchedule.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem localScheduledSeedNext_event (pass : ℕ) (seed : Seed)
--       (hseed : physicalSeedGood source target (scheduledSeedFactor N pass) seed)
--       (event : Set Seed) :
--       (localScheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
--         {draw | localScheduledSeedNext (R := R) source target N P T S H pass seed draw ∈ event} =
--       (scheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
--         {draw | scheduledSeedNext (R := R) source target N P T S H pass seed draw ∈ event}
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalLocalProgramKey` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.LocalScheduledSeedDraw`, `OAI.EditApproximation.PhysicalLocalProgramCoordinate`, `OAI.EditApproximation.PhysicalLocalProgramDraw`, `OAI.EditApproximation.PhysicalProgramCoordinate`, `OAI.EditApproximation.PhysicalProgramDraw`, `OAI.EditApproximation.PhysicalProgramKey`, `OAI.EditApproximation.ScheduledSeedDraw` and `OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalSeedGood` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.localScheduledSeedDrawLaw`, `OAI.EditApproximation.localScheduledSeedNext`, `OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace`, `OAI.EditApproximation.scheduledSeedDrawLaw` and `OAI.EditApproximation.scheduledSeedNext` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.smallLogExponent`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.scheduledSeedFactor` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.ClampedPhysicalSeed` and `OAI.EditApproximation.clampedSeedNat` (the published bundle `Def_EditApproxScheme_10`).
--
--   **Used by.** The proof of `OAI.EditApproximation.localFinalProgram_accuracy` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Geometry/LocalSeedSchedule.lean (declaration OAI.EditApproximation.localScheduledSeedNext_event)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
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

include hN hPeq hsize in
theorem localScheduledSeedNext_event (pass : ℕ) (seed : Seed)
    (hseed : physicalSeedGood source target (scheduledSeedFactor N pass) seed)
    (event : Set Seed) :
    (localScheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | localScheduledSeedNext (R := R) source target N P T S H pass seed draw ∈ event} =
    (scheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | scheduledSeedNext (R := R) source target N P T S H pass seed draw ∈ event} := by
  sorry

end Program

end EditApproximation

end OAI
end
