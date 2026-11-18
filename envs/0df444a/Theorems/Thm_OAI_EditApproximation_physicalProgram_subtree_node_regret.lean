-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalProgram_subtree_node_regret
-- name    : OAI.EditApproximation.physicalProgram_subtree_node_regret
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:38:07.896246+00:00
-- url     : https://prove2.me/theorems/32b7d182-5624-4479-8399-d4a1637ecdc8
-- title:
--   OAI.EditApproximation.physicalProgram_subtree_node_regret: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalProgram_subtree_node_regret` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramSubtreeRegret.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramSubtreeRegret.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem physicalProgram_subtree_node_regret (S : ℕ) (d : Fin K) (path : TreeLayer M d.val)
--       (hnotbad : ¬ (comparisonActiveScale source target (frontier d.val path) <
--         heightQuarterRoot N * (charges d path).1 ∨
--         comparisonActiveScale source target (frontier d.val path) < heightQuarterRoot N * (charges d path).2))
--       (hvelocity : |prediction d path| ≤ 1 - tau) :
--       (∫ draw : Draw, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
--         (choices draw) root K rootQ t d path) ∂globalLaw) ≤
--         physicalProgramNodeCoefficient N F η κ delta S H * comparisonActiveCost source target (frontier d.val path)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.FiniteBernsteinInput` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.computed_program_grid_lower`, `OAI.EditApproximation.heightQuarterRoot`, `OAI.EditApproximation.physicalProgramNodeCoefficient` and `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.PhysicalProgramCoordinate`, `OAI.EditApproximation.PhysicalProgramDraw`, `OAI.EditApproximation.PhysicalProgramKey`, `OAI.EditApproximation.comparisonActiveCost`, `OAI.EditApproximation.comparisonActiveScale`, `OAI.EditApproximation.comparisonFrontier`, `OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace` and `OAI.EditApproximation.physicalProgramDrawLaw` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalProgramDrawSelections`, `OAI.EditApproximation.subtreeComparisonCharges`, `OAI.EditApproximation.subtreeComparisonPrediction` and `OAI.EditApproximation.subtreeComparisonTreeRegret` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.smallLogExponent`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalNode` and `OAI.EditApproximation.TreeLayer` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.physicalSource` and `OAI.EditApproximation.physicalSourceInterval` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.groupDyadicScales` and `OAI.EditApproximation.groupSampleCount` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.groupDyadicScaleAt` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.localFinalProgram_accuracy` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramSubtreeRegret.lean (declaration OAI.EditApproximation.physicalProgram_subtree_node_regret)

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section Comparison

variable {α : Type*} [DecidableEq α] {M J R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hM : 0 < M) (hMeq : M = (integerParameters N).M)
  (U : PhysicalEntry M J target.length → ℕ) (P : ℕ) (hPeq : P = (integerParameters N).P)
  (A : ℚ) (hA : 1 ≤ A) (hAupper : A ≤ (integerParameters N).initialFactor)
  (hsize : source.length + target.length ≤ N)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (hHeq : H = inputHeight N) (hH : 4 ≤ H)
  (delta η κ : ℚ) (hdelta : 0 < delta) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
  (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * inputSmallLog N : ℚ) : ℝ) *
    (((2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ))) : ℝ)) ≤ (κ : ℝ))
  (herror : 2 * (rationalParameters (inputSmallLog N)).gamma +
    512 * (128 * inputSmallLog N : ℚ) * inputSmallLog N *
      (2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ)) ≤ κ * delta)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))
  (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "F" => inputSmallLog N
local notation "thetaExponent" => 40 * smallLogExponent N
local notation "tau" => RationalParameters.tau (rationalParameters F)
local notation "hP" => computed_program_grid_lower N P hN hPeq
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "charges" => subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ
local notation "prediction" => subtreeComparisonPrediction source target hM U N P F A hP T root K hheight rootQ
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H (F ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H (F ^ 80) tau η κ
local notation "globalLaw" => physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H (F ^ 80) tau

include hell hM hMeq hA hAupper hsize hseed hT hHeq hH hdelta hη hκ hκhalf hηrange herror bernstein

theorem physicalProgram_subtree_node_regret (S : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (hnotbad : ¬ (comparisonActiveScale source target (frontier d.val path) <
      heightQuarterRoot N * (charges d path).1 ∨
      comparisonActiveScale source target (frontier d.val path) < heightQuarterRoot N * (charges d path).2))
    (hvelocity : |prediction d path| ≤ 1 - tau) :
    (∫ draw : Draw, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
      (choices draw) root K rootQ t d path) ∂globalLaw) ≤
      physicalProgramNodeCoefficient N F η κ delta S H * comparisonActiveCost source target (frontier d.val path) := by
  sorry

end Comparison

end EditApproximation

end OAI
end
