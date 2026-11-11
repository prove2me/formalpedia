-- Prove2me | Theorems.Thm_OAI_SharpIntegralFillings_IntegerChart_exists_scalar_straightened_charts
-- name    : OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T13:34:10.003336+00:00
-- url     : https://prove2.me/theorems/c8a1fd40-2d5d-42ed-aab5-1f55c731da94
-- title:
--   OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpIntegralFillings.coefficient_optimal`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts` of [lean/OAI/Geometry/IntegralFillings/Charts/ScalarPieces.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/IntegralFillings/Charts/ScalarPieces.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpIntegralFillings.IntegerChart`, with `open Set MeasureTheory Measure Filter Module`, `open Set Filter MeasureTheory Measure ContinuousLinearMap`, `open scoped Topology Convolution NNReal`, `open Set Filter MeasureTheory Measure Metric`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open Set MeasureTheory Filter`, `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal`, `open Filter Set`, `open scoped Topology NNReal`, `open Set Filter MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set Metric`, `open scoped Topology Pointwise NNReal`, `open Set MeasureTheory`, `open scoped RealInnerProductSpace`, `open Matrix`, `open scoped RealInnerProductSpace MatrixOrder`, `open Set MeasureTheory Filter BorelRestriction EuclideanStraightening`, `open scoped Topology NNReal ENNReal`):
--
--   ```lean
--   theorem exists_scalar_straightened_charts (C : IntegerChart X (k+1))
--       {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
--       ∃ D : ℕ → IntegerChart X (k+1),
--         Pairwise (fun i j => Disjoint (D i).image (D j).image) ∧
--         (∀ i, (D i).image ⊆ C.image) ∧
--         (∀ i z (hz : z ∈ (D i).domain),
--           u ((D i).param ⟨z,hz⟩) = (Prism.split k z).1) ∧
--         Summable (fun i => mass (D i).action) ∧
--         (∑' i, mass (D i).action) ≤ mass C.action ∧
--         ∀ b π, Admissible b π →
--           C.action b (Matrix.vecCons u π) = ∑' i, (D i).action b (Matrix.vecCons u π)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpIntegralFillings.Prism.Euc` and `OAI.SharpIntegralFillings.Prism.split` (definitions bundle `OAIQ219IF000` of this split); `OAI.SharpIntegralFillings.Admissible`, `OAI.SharpIntegralFillings.Euc`, `OAI.SharpIntegralFillings.IntegerChart`, `OAI.SharpIntegralFillings.mass`, `OAI.SharpIntegralFillings.IntegerChart.action` and `OAI.SharpIntegralFillings.IntegerChart.image` (the published bundle `Def_FillingCoefficient`).
--
--   **Used by.** The proof of `OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/IntegralFillings/Charts/ScalarPieces.lean (declaration OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts)

import Mathlib
import Definitions.Def_FillingCoefficient
import Definitions.Def_OAIQ219IF000

section

attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter BorelRestriction EuclideanStraightening
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

theorem exists_scalar_straightened_charts (C : IntegerChart X (k+1))
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ D : ℕ → IntegerChart X (k+1),
      Pairwise (fun i j => Disjoint (D i).image (D j).image) ∧
      (∀ i, (D i).image ⊆ C.image) ∧
      (∀ i z (hz : z ∈ (D i).domain),
        u ((D i).param ⟨z,hz⟩) = (Prism.split k z).1) ∧
      Summable (fun i => mass (D i).action) ∧
      (∑' i, mass (D i).action) ≤ mass C.action ∧
      ∀ b π, Admissible b π →
        C.action b (Matrix.vecCons u π) = ∑' i, (D i).action b (Matrix.vecCons u π) := by
  sorry

end SharpIntegralFillings.IntegerChart

end

end OAI
end
