-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_original_product_graph_integral_bound
-- name    : OAI.PlanarFalconer.original_product_graph_integral_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:59:46.130818+00:00
-- url     : https://prove2.me/theorems/195bcc62-e7d4-4506-ad4d-96a2cf186a5d
-- title:
--   OAI.PlanarFalconer.original_product_graph_integral_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.original_product_graph_integral_bound` of [lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ProductGraphIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ProductGraphIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ComplexConjugate`):
--
--   ```lean
--   theorem original_product_graph_integral_bound
--       (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
--       (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a)
--       {θ : ℝ} (hθ : 0 < θ) (I : Finset GraphNonedgeIndex)
--       (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ) A B)
--       {d : ℝ} (hd : 0 ≤ d)
--       (hdegree : ∀ j k s reverse row,
--         ((activeProductMatrixNeighbors I (a+n) j k θ s reverse row).card : ℝ) ≤ d)
--       {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
--       (β γ : Plane → UnitCircle → ℂ)
--       (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
--       (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
--       {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
--       (hbβ : ∀ x u, ‖β x u‖ ≤ B₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ B₂)
--       (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
--       (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
--       {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
--       let U := fun P : CellPath => fun z : ℝ × UnitCircle =>
--         sourceAngularTransform ρ (Q₁.descendant P).carrier M₁ β z.1 z.2
--       let V := fun Q : CellPath => fun z : ℝ × UnitCircle =>
--         sourceAngularTransform ν (Q₂.descendant Q).carrier M₂ γ z.1 z.2
--       ‖((2:ℝ)^(2*(v-(a+n)))) •
--         ∑ e ∈ I, graphOriginalTerm ![ρ,ρ,ν,ν]
--           (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
--           ![M₁,M₁,M₂,M₂] ![β,β,γ,γ] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ‖ ≤
--         d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
--           (sourceAngularH (a+n) v Ψ (U row.1) (V row.2)).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.GraphCellQuadIndex`, `OAI.PlanarFalconer.GraphNonedgeIndex`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.activeProductMatrixNeighbors`, `OAI.PlanarFalconer.angularBinCount`, `OAI.PlanarFalconer.graphQuadCells`, `OAI.PlanarFalconer.sourceAngularH`, `OAI.PlanarFalconer.sourceAngularTransform`, `OAI.PlanarFalconer.sourceProductVertices`, `OAI.PlanarFalconer.DyadicSquare.carrier` and `OAI.PlanarFalconer.DyadicSquare.descendant` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.graphOriginalTerm` and `OAI.PlanarFalconer.sourceProductGraphIndices` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_product_estimate` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ProductGraphIntegral.lean (declaration OAI.PlanarFalconer.original_product_graph_integral_bound)

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
open scoped ComplexConjugate

theorem original_product_graph_integral_bound
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a)
    {θ : ℝ} (hθ : 0 < θ) (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ) A B)
    {d : ℝ} (hd : 0 ≤ d)
    (hdegree : ∀ j k s reverse row,
      ((activeProductMatrixNeighbors I (a+n) j k θ s reverse row).card : ℝ) ≤ d)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ B₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ B₂)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    let U := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform ρ (Q₁.descendant P).carrier M₁ β z.1 z.2
    let V := fun Q : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform ν (Q₂.descendant Q).carrier M₂ γ z.1 z.2
    ‖((2:ℝ)^(2*(v-(a+n)))) •
      ∑ e ∈ I, graphOriginalTerm ![ρ,ρ,ν,ν]
        (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![β,β,γ,γ] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (sourceAngularH (a+n) v Ψ (U row.1) (V row.2)).toReal := by
  sorry

end PlanarFalconer

end OAI
end
