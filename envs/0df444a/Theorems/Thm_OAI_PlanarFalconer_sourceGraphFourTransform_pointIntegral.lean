-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_sourceGraphFourTransform_pointIntegral
-- name    : OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:01:10.435868+00:00
-- url     : https://prove2.me/theorems/61a3616f-9473-4c33-a905-5378cf21cd46
-- title:
--   OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral` of [lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphFourTransformPointIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphFourTransformPointIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem sourceGraphFourTransform_pointIntegral
--       (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
--       (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
--       (b : Fin 4 → Plane → UnitCircle → ℂ)
--       (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
--       (hbcont : ∀ i x, Continuous (b i x))
--       (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
--       (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ)
--       {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
--       ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
--         sourceGraphFourTransform ρ X M b (graphSourceWeight distance plus axis (angularBinCount δ) j k) r u w
--           ∂sourceArcLength ∂sourceArcLength) =
--       ((M 0*M 1)*(M 2*M 3))⁻¹ •
--         (∫ x, graphPointIntegral (graphAmplitudePullback b x distance plus axis δ j k Ψ)
--           v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)
--           ∂Measure.pi (fun i => (ρ i).restrict (X i)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.angularBinCount`, `OAI.PlanarFalconer.graphSourceSign`, `OAI.PlanarFalconer.graphSourceWeight` and `OAI.PlanarFalconer.sourceArcLength` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.graphAmplitudePullback`, `OAI.PlanarFalconer.graphPointIntegral` and `OAI.PlanarFalconer.sourceGraphFourTransform` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_regularized_original_graph_removal` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphFourTransformPointIntegral.lean (declaration OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceGraphFourTransform_pointIntegral
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hbcont : ∀ i x, Continuous (b i x))
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      sourceGraphFourTransform ρ X M b (graphSourceWeight distance plus axis (angularBinCount δ) j k) r u w
        ∂sourceArcLength ∂sourceArcLength) =
    ((M 0*M 1)*(M 2*M 3))⁻¹ •
      (∫ x, graphPointIntegral (graphAmplitudePullback b x distance plus axis δ j k Ψ)
        v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)
        ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  sorry

end PlanarFalconer

end OAI
end
