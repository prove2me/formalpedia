-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalNode_firstCrossing_regret
-- name    : OAI.EditApproximation.physicalNode_firstCrossing_regret
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:39.573226+00:00
-- url     : https://prove2.me/theorems/fdffa6e2-eaa1-4681-9128-101c2845f002
-- title:
--   OAI.EditApproximation.physicalNode_firstCrossing_regret: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalNode_firstCrossing_regret` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalNodeRegret.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalNodeRegret.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset`):
--
--   ```lean
--   theorem physicalNode_firstCrossing_regret
--       (hleaf : ¬ (parent).hi - (parent).lo ≤ 1)
--       (b thetaExponent Q : ℕ) (tau gamma κ : ℚ) (htau : 0 < tau)
--       (hdelta : 0 < delta) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (cell : ℕ × ℕ)
--       (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
--       (specified : UnskippedBand source target parent b P thetaExponent tau F
--         (physicalBandChildMassTable source target U N P F A T node hbelow)
--         (physicalBandChildInitial source target U N P F A node hbelow))
--       (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell)
--       (hrep : (b, specified.center) ∈ representatives)
--       (q : TargetInterval target.length)
--       (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
--       (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
--       (sample : ℕ → Fin M → TargetInterval target.length) (hsample : ∀ t, sample t ∈ specified.actions)
--       (draw : ℕ → ∀ scale : Fin (groupDyadicScales M b F).length,
--         Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
--       (honline : ∀ t, sharedBandRationalAction specified.center (sample t) ∈ online t q)
--       (hselected : ∀ t, (physicalNodeSelectedGroup source target U N P F A T delta choices node hbelow
--         b thetaExponent Q tau cell hnonempty t (draw t)).rationalAction ∈ groups t)
--       (herror : 2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
--       (S : ℕ) :
--       let c : ℝ := stateEditCost (physicalSource source node) target q
--       let charge : ℝ := (L : ℝ) * targetEndpointDistance q specified.center
--       let clipped := physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison
--       let failure := fun t => physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
--         b thetaExponent Q tau cell t (draw t) gamma
--       let crossing := firstCrossing specified.actions.toFinset S
--         (fun t => bandActionCost charge (fun t coordinate => (history t coordinate : ℝ)) (t + 1)) c
--       (∑ t ∈ range S,
--         (max c (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
--           charge - clipped (t + 1))) ≤
--         (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
--           (fun t coordinate => (history t coordinate : ℝ)) clipped sample t) +
--             2 * (delta : ℝ) * c + 2 * (F : ℝ) * c *
--               ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalSelections`, `OAI.EditApproximation.physicalBandChildInitial` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.bandActionCost`, `OAI.EditApproximation.firstCrossing`, `OAI.EditApproximation.sampledPrefixRegret` and `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.physicalBandChildMassTable` and `OAI.EditApproximation.physicalRefinement` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalBandHistory`, `OAI.EditApproximation.physicalComparisonClipped`, `OAI.EditApproximation.physicalNodeCellBands`, `OAI.EditApproximation.physicalNodeGroupFailure`, `OAI.EditApproximation.physicalNodeGroups`, `OAI.EditApproximation.physicalNodeOnline` and `OAI.EditApproximation.physicalNodeSelectedGroup` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.RationalBellmanAction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalNode` and `OAI.EditApproximation.TreeLayer` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.targetEndpointDistance` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.PhysicalRationalAction`, `OAI.EditApproximation.physicalSource` and `OAI.EditApproximation.physicalSourceInterval` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.groupDyadicScales`, `OAI.EditApproximation.groupSampleCount`, `OAI.EditApproximation.instDecidableEqTargetInterval` and `OAI.EditApproximation.sharedBandRationalAction` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.UnskippedBand` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.groupDyadicScaleAt`, `OAI.EditApproximation.UnskippedBand.actions` and `OAI.EditApproximation.UnskippedBand.rationalAction` (the published bundle `Def_EditApproxScheme_13`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physical_conditional_node_regret` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalNodeRegret.lean (declaration OAI.EditApproximation.physicalNode_firstCrossing_regret)

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

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset

section PhysicalNode

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "groups" => physicalNodeGroups source target U N P F A T delta choices node hbelow
local notation "online" => physicalNodeOnline source target U N P F A T delta choices node hbelow
local notation "cone" => physicalNodeCone source target U N P F A T delta choices node hbelow
local notation "onlineValue" => physicalNodeOnlineValue source target U N P F A T delta choices node hbelow
local notation "parent" => physicalSourceInterval source.length node
local notation "representatives" => stageRepresentatives source target U N P F A node
local notation "L" => (128 * F : ℚ)

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

include hM hsize hP hF hA hseed hT in
theorem physicalNode_firstCrossing_regret
    (hleaf : ¬ (parent).hi - (parent).lo ≤ 1)
    (b thetaExponent Q : ℕ) (tau gamma κ : ℚ) (htau : 0 < tau)
    (hdelta : 0 < delta) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (specified : UnskippedBand source target parent b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell)
    (hrep : (b, specified.center) ∈ representatives)
    (q : TargetInterval target.length)
    (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
    (sample : ℕ → Fin M → TargetInterval target.length) (hsample : ∀ t, sample t ∈ specified.actions)
    (draw : ℕ → ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (honline : ∀ t, sharedBandRationalAction specified.center (sample t) ∈ online t q)
    (hselected : ∀ t, (physicalNodeSelectedGroup source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell hnonempty t (draw t)).rationalAction ∈ groups t)
    (herror : 2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
    (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node) target q
    let charge : ℝ := (L : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison
    let failure := fun t => physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell t (draw t) gamma
    let crossing := firstCrossing specified.actions.toFinset S
      (fun t => bandActionCost charge (fun t coordinate => (history t coordinate : ℝ)) (t + 1)) c
    (∑ t ∈ range S,
      (max c (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
        charge - clipped (t + 1))) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped sample t) +
          2 * (delta : ℝ) * c + 2 * (F : ℝ) * c *
            ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0) := by
  sorry

end PhysicalNode

end EditApproximation

end OAI
end
