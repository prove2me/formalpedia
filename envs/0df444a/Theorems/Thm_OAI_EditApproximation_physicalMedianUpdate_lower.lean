-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalMedianUpdate_lower
-- name    : OAI.EditApproximation.physicalMedianUpdate_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:42.692588+00:00
-- url     : https://prove2.me/theorems/45c0ae3a-12a8-4815-882f-65c395422014
-- title:
--   OAI.EditApproximation.physicalMedianUpdate_lower: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalMedianUpdate_lower` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalSeedPass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalSeedPass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset MeasureTheory ProbabilityTheory`):
--
--   ```lean
--    theorem physicalMedianUpdate_lower (draws : Fin copies → Draw) (state : PhysicalEntry M J target.length) :
--       stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.PhysicalProgramDraw` and `OAI.EditApproximation.physicalMedianUpdate` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalProgramDrawSelections` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.refinementFactor`, `OAI.EditApproximation.smallLogExponent`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalNode` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` and `OAI.EditApproximation.physicalSource` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proof of `OAI.EditApproximation.localFinalProgram_accuracy` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalSeedPass.lean (declaration OAI.EditApproximation.physicalMedianUpdate_lower)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section Pass

variable {α : Type*} [DecidableEq α] {M J R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (U : PhysicalEntry M J target.length → ℕ) (P : ℕ) (hPeq : P = (integerParameters N).P)
  (A : ℚ) (hA : 1 ≤ A) (hAupper : A ≤ (integerParameters N).initialFactor)
  (hsize : source.length + target.length ≤ N)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T S : ℕ) (hTeq : T = (integerParameters N).T) (hSeq : S = (integerParameters N).S)
  (hHeq : H = inputHeight N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))
  (a copies : ℕ) (ha : (a : ℚ) = refinementFactor A (inputSmallLog N)) (hcopies : 0 < copies)

local notation "ell" => inputSmallLog N
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P ell A T thetaExponent H (ell ^ 80) tau eta kappa
local notation "update" => physicalMedianUpdate source target U N P ell A T delta a S copies choices

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
include hN hell hPeq hA hsize hseed hTeq ha hcopies in
 theorem physicalMedianUpdate_lower (draws : Fin copies → Draw) (state : PhysicalEntry M J target.length) :
    stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state := by
  sorry

end Pass

end EditApproximation

end OAI
end
