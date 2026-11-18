-- Prove2me | Theorems.Thm_OAI_EditApproximation_subtree_expected_excess_of_good_nodes
-- name    : OAI.EditApproximation.subtree_expected_excess_of_good_nodes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:37:52.092545+00:00
-- url     : https://prove2.me/theorems/523b7cfb-8776-4875-aae5-35d48f8863b2
-- title:
--   OAI.EditApproximation.subtree_expected_excess_of_good_nodes: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.subtree_expected_excess_of_good_nodes` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalSubtreeBudget.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalSubtreeBudget.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset MeasureTheory ProbabilityTheory`):
--
--   ```lean
--    theorem subtree_expected_excess_of_good_nodes (ratio : ℝ) (hratio : 0 < ratio)
--       (tau : ℚ) (htau : 0 ≤ tau)
--       (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
--       (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
--       (S : ℕ) (hS : 0 < S) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
--       (hgood : ∀ (d : Fin K) (path : TreeLayer M d.val),
--         ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
--           comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
--         |prediction d path| ≤ 1 - tau →
--         (∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
--           (choices ω) root K rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
--       (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω)
--           root S rootQ : ℝ) -
--         stateEditCost (physicalSource source root) target rootQ) 0 ∂μ) ≤
--         ((8 * (M : ℝ) + 512 * F) * K / P +
--           (40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) +
--             2 * K * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) / S) *
--           stateEditCost (physicalSource source root) target rootQ
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.PhysicalSelections` and `OAI.EditApproximation.stageRepresentatives` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.stateEditCost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.comparisonActiveCost`, `OAI.EditApproximation.comparisonActiveScale`, `OAI.EditApproximation.comparisonFrontier` and `OAI.EditApproximation.physicalRefinement` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.subtreeComparisonCharges`, `OAI.EditApproximation.subtreeComparisonPrediction` and `OAI.EditApproximation.subtreeComparisonTreeRegret` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.refinementFactor` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalNode` and `OAI.EditApproximation.TreeLayer` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry`, `OAI.EditApproximation.physicalSource` and `OAI.EditApproximation.physicalSourceInterval` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proof of `OAI.EditApproximation.localFinalProgram_accuracy` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalSubtreeBudget.lean (declaration OAI.EditApproximation.subtree_expected_excess_of_good_nodes)

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
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

section Tree

variable {α Ω : Type*} [DecidableEq α] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {M J : ℕ} (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : Ω → PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "charges" => subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ
local notation "prediction" => subtreeComparisonPrediction source target hM U N P F A hP T root K hheight rootQ
local notation "D" => comparisonStateCost source target
  (some (physicalSourceInterval source.length root, rootQ))

include hsize hF hA hseed hT in
 theorem subtree_expected_excess_of_good_nodes (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (hS : 0 < S) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin K) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) root K rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω)
        root S rootQ : ℝ) -
      stateEditCost (physicalSource source root) target rootQ) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * K / P +
        (40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) +
          2 * K * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) / S) *
        stateEditCost (physicalSource source root) target rootQ := by
  sorry

end Tree

end EditApproximation

end OAI
end
