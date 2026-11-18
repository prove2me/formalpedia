-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalProgram_conditional_node_regret
-- name    : OAI.EditApproximation.physicalProgram_conditional_node_regret
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:44:43.981468+00:00
-- url     : https://prove2.me/theorems/e71cd7d4-67a8-4cd1-88f1-07ac0530d3b9
-- title:
--   OAI.EditApproximation.physicalProgram_conditional_node_regret: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalProgram_conditional_node_regret` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramNodeRegret.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramNodeRegret.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem physicalProgram_conditional_node_regret (draw : Draw) (S : ℕ) :
--       let c : ℝ := stateEditCost (physicalSource source node.1) target q
--       let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
--       let clipped := physicalComparisonClipped source target U N P F A T delta (choices draw) node.1 node.2 comparison
--       (∫ fresh : Fresh, (∑ t ∈ range S, (max c
--         (physicalRefinement source target U N P F A T delta (choices (refresh draw onlineKey groupKey fresh))
--           node.1 (t + 1) q : ℝ) - charge - clipped (t + 1))) ∂localLaw) ≤
--         ((∑ child, specified.envelope child : ℚ) : ℝ) *
--           (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
--             (S : ℝ) / (H : ℝ) ^ 3) +
--           2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.FiniteBernsteinInput`, `OAI.EditApproximation.physicalBandChildInitial` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.PhysicalGroupArray`, `OAI.EditApproximation.PhysicalGroupKey`, `OAI.EditApproximation.PhysicalOnlineArray`, `OAI.EditApproximation.PhysicalOnlineKey`, `OAI.EditApproximation.PhysicalProgramCoordinate`, `OAI.EditApproximation.PhysicalProgramDraw`, `OAI.EditApproximation.physicalBandChildMassTable`, `OAI.EditApproximation.physicalProgramCells`, `OAI.EditApproximation.physicalProgramCoordinateLaw`, `OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace` and `OAI.EditApproximation.physicalRefinement` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalProgramOnlineGuard` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.physicalComparisonClipped`, `OAI.EditApproximation.physicalNodeCellBands`, `OAI.EditApproximation.physicalProgramDrawSelections` and `OAI.EditApproximation.physicalProgramRefresh` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.dyadicScales`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.smallLogExponent`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalInternalNode`, `OAI.EditApproximation.PhysicalNode`, `OAI.EditApproximation.TreeLayer` and `OAI.EditApproximation.bandCoordinates` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.targetEndpointDistance` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.physicalSource` and `OAI.EditApproximation.physicalSourceInterval` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.groupDyadicScales`, `OAI.EditApproximation.groupSampleCount` and `OAI.EditApproximation.instDecidableEqTargetInterval` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.UnskippedBand` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.groupDyadicScaleAt`, `OAI.EditApproximation.UnskippedBand.actions` and `OAI.EditApproximation.UnskippedBand.envelope` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalProgram_global_node_regret` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalProgramNodeRegret.lean (declaration OAI.EditApproximation.physicalProgram_conditional_node_regret)

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
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

section Node

variable {α : Type*} [DecidableEq α]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
  {M J P F b Q thetaExponent R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (hM : 0 < M) (hMeq : M = (integerParameters N).M)
  (hPeq : P = (integerParameters N).P) (hFeq : F = inputSmallLog N)
  (eb : ℕ) (hbeq : b = 2 ^ eb) (hQeq : Q = inputSmallLog N ^ 80)
  (hthetaeq : thetaExponent = 40 * smallLogExponent N) (hHeq : H = inputHeight N) (hH : 4 ≤ H)
  (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta η κ : ℚ)
  (hdelta : 0 < delta) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
  (node : PhysicalInternalNode M J)
  (hleaf : ¬ (physicalSourceInterval source.length node.1).hi -
    (physicalSourceInterval source.length node.1).lo ≤ 1)
  (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
  (scale : Fin (dyadicScales N).length) (hscale : (dyadicScales N).get scale = b)
  (cell : ℕ × ℕ)
  (cellIndex : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).length)
  (hcell : (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).get cellIndex = cell)
  (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent
    (rationalParameters F).tau cell ≠ [])
  (specified : UnskippedBand source target (physicalSourceInterval source.length node.1)
    b P thetaExponent (rationalParameters F).tau F
    (physicalBandChildMassTable source target U N P F A T node.1 node.2)
    (physicalBandChildInitial source target U N P F A node.1 node.2))
  (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent
    (rationalParameters F).tau cell)
  (hget : (stageRepresentatives source target U N P F A node.1).get representative = (b, specified.center))
  (q : TargetInterval target.length) (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node.1) target q)
  (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, specified.center))
  (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
  (htau : 0 < (rationalParameters F).tau)
  (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) *
    (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (κ : ℝ))
  (herror : 2 * (rationalParameters F).gamma +
    512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
  (bernstein : ∀ h : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
    (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

local notation "tau" => RationalParameters.tau (rationalParameters F)
local notation "onlineKey" => (Sigma.mk node representative : PhysicalOnlineKey source target U N P F A)
local notation "groupKey" => (Sigma.mk node (Sigma.mk scale cellIndex) : PhysicalGroupKey source target U N P F A thetaExponent)
local notation "bandG" => physicalProgramBandG source target U N P F A T thetaExponent H tau node representative
local notation "bandK" => physicalProgramBandK source target U N P F A T thetaExponent H tau node representative
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau
local notation "Fresh" => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau onlineKey ×
  PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q groupKey
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
local notation "refresh" => physicalProgramRefresh source target U N P F A T thetaExponent H Q tau
local notation "localLaw" =>
  Measure.prod (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (Sum.inl onlineKey))
    (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (Sum.inr groupKey))

include hN hell hM hMeq hPeq hFeq hbeq hQeq hthetaeq hHeq hH hsize hP hF hA hseed hT
  hdelta hη hκ hκhalf hleaf hscale hcell hnonempty hspecified hget hb hquery hc htau hηrange herror bernstein

theorem physicalProgram_conditional_node_regret (draw : Draw) (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node.1) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta (choices draw) node.1 node.2 comparison
    (∫ fresh : Fresh, (∑ t ∈ range S, (max c
      (physicalRefinement source target U N P F A T delta (choices (refresh draw onlineKey groupKey fresh))
        node.1 (t + 1) q : ℝ) - charge - clipped (t + 1))) ∂localLaw) ≤
      ((∑ child, specified.envelope child : ℚ) : ℝ) *
        (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c := by
  sorry

end Node

end EditApproximation

end OAI
end
