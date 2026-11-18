-- Prove2me | Theorems.Thm_OAI_EditApproximation_physical_conditional_node_regret
-- name    : OAI.EditApproximation.physical_conditional_node_regret
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:10.653941+00:00
-- url     : https://prove2.me/theorems/70df0449-a11a-4645-a122-11996d381cb6
-- title:
--   OAI.EditApproximation.physical_conditional_node_regret: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physical_conditional_node_regret` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalConditionalNode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalConditionalNode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem physical_conditional_node_regret {α : Type*} [DecidableEq α]
--       (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
--       {M J P F b Q thetaExponent R H G K : ℕ}
--       [NeZero M] [NeZero R] [NeZero (optimizerTriangularMass K)]
--       [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
--       (hM : 0 < M) (hMeq : M = (integerParameters N).M)
--       (hPeq : P = (integerParameters N).P) (hFeq : F = inputSmallLog N)
--       (eb : ℕ) (hbeq : b = 2 ^ eb) (hQeq : Q = inputSmallLog N ^ 80)
--       (hthetaeq : thetaExponent = 40 * smallLogExponent N) (hHeq : H = inputHeight N) (hH : 4 ≤ H)
--       (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
--       (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
--       (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
--         (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
--       (T : ℕ) (hT : 0 < T) (delta η κ : ℚ)
--       (hdelta : 0 < delta) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
--       (reference : PhysicalSelections M J source.length target.length P
--         (stageRepresentatives source target U N P F A))
--       (node : PhysicalNode M J) (hbelow : node.1.val < J)
--       (hleaf : ¬ (physicalSourceInterval source.length node).hi -
--         (physicalSourceInterval source.length node).lo ≤ 1)
--       (cell : ℕ × ℕ)
--       (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent
--         (rationalParameters F).tau cell ≠ [])
--       (specified : UnskippedBand source target (physicalSourceInterval source.length node)
--         b P thetaExponent (rationalParameters F).tau F
--         (physicalBandChildMassTable source target U N P F A T node hbelow)
--         (physicalBandChildInitial source target U N P F A node hbelow))
--       (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent
--         (rationalParameters F).tau cell)
--       (hrep : (b, specified.center) ∈ stageRepresentatives source target U N P F A node)
--       (q : TargetInterval target.length)
--       (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
--       (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
--       (hG : G = H + (bandCoordinates specified.actions.toFinset).card + 2) (hK : K = G ^ 80)
--       (htau : 0 < (rationalParameters F).tau)
--       (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) *
--         (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (κ : ℝ))
--       (herror : 2 * (rationalParameters F).gamma +
--         512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
--       (realizations : BandParentSpace R M b F Q K → PhysicalSelections M J source.length target.length P
--         (stageRepresentatives source target U N P F A))
--       (hgroupsFixed : ∀ ω label, node.1.val < label.1.val →
--         (realizations ω).groups label = reference.groups label)
--       (honlineFixed : ∀ ω label, node.1.val < label.1.val →
--         (realizations ω).online label = reference.online label)
--       (honlineWire : ∀ ω t, sharedBandRationalAction specified.center
--         (physicalBandOnlineDraw source target U N P F A T delta reference node hbelow
--           b thetaExponent (rationalParameters F).tau specified.center specified.nonempty η κ G K t
--             (parentOnlineDraw ω t)) ∈
--         physicalNodeOnline source target U N P F A T delta (realizations ω) node hbelow t q)
--       (hgroupWire : ∀ ω t,
--         (physicalNodeSelectedGroup source target U N P F A T delta reference node hbelow
--           b thetaExponent Q (rationalParameters F).tau cell hnonempty t (parentGroupDraw ω t)).rationalAction ∈
--         physicalNodeGroups source target U N P F A T delta (realizations ω) node hbelow t)
--       (bernstein : ∀ scale : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
--         (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) =>
--           (PMF.uniformOfFintype (Fin M)).toMeasure)) (S : ℕ) :
--       let c : ℝ := stateEditCost (physicalSource source node) target q
--       let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
--       let clipped := physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison
--       (∫ ω, (∑ t ∈ range S,
--         (max c (physicalRefinement source target U N P F A T delta (realizations ω) node (t + 1) q : ℝ) -
--           charge - clipped (t + 1))) ∂bandParentLaw R M b F Q K) ≤
--         ((∑ child, specified.envelope child : ℚ) : ℝ) *
--           (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
--             (S : ℝ) / (H : ℝ) ^ 3) +
--           2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BandParentSpace`, `OAI.EditApproximation.FiniteBernsteinInput`, `OAI.EditApproximation.ParentGroupDraw`, `OAI.EditApproximation.PhysicalSelections`, `OAI.EditApproximation.physicalBandChildInitial` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.bandParentLaw`, `OAI.EditApproximation.physicalBandChildMassTable` and `OAI.EditApproximation.physicalRefinement` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.parentGroupDraw` and `OAI.EditApproximation.parentOnlineDraw` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.physicalBandOnlineDraw`, `OAI.EditApproximation.physicalComparisonClipped`, `OAI.EditApproximation.physicalNodeCellBands`, `OAI.EditApproximation.physicalNodeGroups`, `OAI.EditApproximation.physicalNodeOnline` and `OAI.EditApproximation.physicalNodeSelectedGroup` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.RationalBellmanAction`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.smallLogExponent`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalNode`, `OAI.EditApproximation.TreeLayer`, `OAI.EditApproximation.bandCoordinates` and `OAI.EditApproximation.optimizerTriangularMass` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.targetEndpointDistance` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalChildTables`, `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.PhysicalRationalAction`, `OAI.EditApproximation.physicalSource` and `OAI.EditApproximation.physicalSourceInterval` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.groupDyadicScales`, `OAI.EditApproximation.groupSampleCount`, `OAI.EditApproximation.instDecidableEqTargetInterval` and `OAI.EditApproximation.sharedBandRationalAction` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.UnskippedBand` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.groupDyadicScaleAt`, `OAI.EditApproximation.UnskippedBand.actions`, `OAI.EditApproximation.UnskippedBand.envelope` and `OAI.EditApproximation.UnskippedBand.rationalAction` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalProgram_conditional_node_regret` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalConditionalNode.lean (declaration OAI.EditApproximation.physical_conditional_node_regret)

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

attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem physical_conditional_node_regret {α : Type*} [DecidableEq α]
    (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M J P F b Q thetaExponent R H G K : ℕ}
    [NeZero M] [NeZero R] [NeZero (optimizerTriangularMass K)]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
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
    (reference : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent
      (rationalParameters F).tau cell ≠ [])
    (specified : UnskippedBand source target (physicalSourceInterval source.length node)
      b P thetaExponent (rationalParameters F).tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent
      (rationalParameters F).tau cell)
    (hrep : (b, specified.center) ∈ stageRepresentatives source target U N P F A node)
    (q : TargetInterval target.length)
    (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
    (hG : G = H + (bandCoordinates specified.actions.toFinset).card + 2) (hK : K = G ^ 80)
    (htau : 0 < (rationalParameters F).tau)
    (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) *
      (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (κ : ℝ))
    (herror : 2 * (rationalParameters F).gamma +
      512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
    (realizations : BandParentSpace R M b F Q K → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (hgroupsFixed : ∀ ω label, node.1.val < label.1.val →
      (realizations ω).groups label = reference.groups label)
    (honlineFixed : ∀ ω label, node.1.val < label.1.val →
      (realizations ω).online label = reference.online label)
    (honlineWire : ∀ ω t, sharedBandRationalAction specified.center
      (physicalBandOnlineDraw source target U N P F A T delta reference node hbelow
        b thetaExponent (rationalParameters F).tau specified.center specified.nonempty η κ G K t
          (parentOnlineDraw ω t)) ∈
      physicalNodeOnline source target U N P F A T delta (realizations ω) node hbelow t q)
    (hgroupWire : ∀ ω t,
      (physicalNodeSelectedGroup source target U N P F A T delta reference node hbelow
        b thetaExponent Q (rationalParameters F).tau cell hnonempty t (parentGroupDraw ω t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta (realizations ω) node hbelow t)
    (bernstein : ∀ scale : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure)) (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison
    (∫ ω, (∑ t ∈ range S,
      (max c (physicalRefinement source target U N P F A T delta (realizations ω) node (t + 1) q : ℝ) -
        charge - clipped (t + 1))) ∂bandParentLaw R M b F Q K) ≤
      ((∑ child, specified.envelope child : ℚ) : ℝ) *
        (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c := by
  sorry

end EditApproximation

end OAI
end
