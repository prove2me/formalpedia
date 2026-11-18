-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalBand_prefix_expected_regret
-- name    : OAI.EditApproximation.physicalBand_prefix_expected_regret
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:37:12.821182+00:00
-- url     : https://prove2.me/theorems/83fe8d3e-aea3-4982-b026-d8550723faf9
-- title:
--   OAI.EditApproximation.physicalBand_prefix_expected_regret: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalBand_prefix_expected_regret` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalExpectedRegret.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalExpectedRegret.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem physicalBand_prefix_expected_regret (htau : 0 < tau) (hdelta : 0 ≤ delta)
--       (hband : band ≠ []) (C S H G K : ℕ) (hCS : C ≤ S) (η κ : ℚ)
--       (hG : G = H + (bandCoordinates (band).toFinset).card + 2) (hK : K = G ^ 80)
--       (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ band)
--       (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
--       (hηrange : (η : ℝ) *
--         (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) ≤ (κ : ℝ)) (charge : ℝ) :
--       (∑ t ∈ range C, uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
--         sampledPrefixRegret charge (κ : ℝ) (fun t coordinate => (history t coordinate : ℝ))
--           (physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison)
--           (fun j => physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
--             b thetaExponent tau r hband η κ G K j integer) t)) ≤
--         ((∑ child, mass child : ℚ) : ℝ) *
--           (Real.log (bandCoordinates (band).toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
--             (S : ℝ) / (H : ℝ) ^ 3)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalSelections` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.sampledPrefixRegret`, `OAI.EditApproximation.stateEditCost` and `OAI.EditApproximation.uniformMean` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.physicalBandActions` and `OAI.EditApproximation.physicalBandEnvelope` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.physicalBandHistory`, `OAI.EditApproximation.physicalBandOnlineDraw` and `OAI.EditApproximation.physicalComparisonClipped` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.PhysicalNode`, `OAI.EditApproximation.TreeLayer`, `OAI.EditApproximation.bandCoordinates` and `OAI.EditApproximation.optimizerTriangularMass` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` and `OAI.EditApproximation.physicalSource` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.instDecidableEqTargetInterval` (the published bundle `Def_EditApproxScheme_08`).
--
--   **Used by.** The proof of `OAI.EditApproximation.physicalProgram_global_node_regret` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalExpectedRegret.lean (declaration OAI.EditApproximation.physicalBand_prefix_expected_regret)

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section PhysicalPrefix

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length)

local notation "band" => physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r
local notation "mass" => physicalBandEnvelope source target U N P F A T node hbelow b thetaExponent tau r
local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

include hM hsize hP hF hA hseed hT in
theorem physicalBand_prefix_expected_regret (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (hband : band ≠ []) (C S H G K : ℕ) (hCS : C ≤ S) (η κ : ℚ)
    (hG : G = H + (bandCoordinates (band).toFinset).card + 2) (hK : K = G ^ 80)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) *
      (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) ≤ (κ : ℝ)) (charge : ℝ) :
    (∑ t ∈ range C, uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      sampledPrefixRegret charge (κ : ℝ) (fun t coordinate => (history t coordinate : ℝ))
        (physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison)
        (fun j => physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
          b thetaExponent tau r hband η κ G K j integer) t)) ≤
      ((∑ child, mass child : ℚ) : ℝ) *
        (Real.log (bandCoordinates (band).toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) := by
  sorry

end PhysicalPrefix

end EditApproximation

end OAI
end
