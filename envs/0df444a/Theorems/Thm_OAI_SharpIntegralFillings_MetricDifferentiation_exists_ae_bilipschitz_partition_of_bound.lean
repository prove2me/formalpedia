-- Prove2me | Theorems.Thm_OAI_SharpIntegralFillings_MetricDifferentiation_exists_ae_bilipschitz_partition_of_bound
-- name    : OAI.SharpIntegralFillings.MetricDifferentiation.exists_ae_bilipschitz_partition_of_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T13:36:09.59079+00:00
-- url     : https://prove2.me/theorems/fa9b3dc7-d9f3-4590-a354-25d049c3ccde
-- title:
--   OAI.SharpIntegralFillings.MetricDifferentiation.exists_ae_bilipschitz_partition_of_bound: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpIntegralFillings.coefficient_optimal`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpIntegralFillings.MetricDifferentiation.exists_ae_bilipschitz_partition_of_bound` of [lean/OAI/Geometry/IntegralFillings/Differentiation/FullRank.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/IntegralFillings/Differentiation/FullRank.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpIntegralFillings.MetricDifferentiation`, with `open Set MeasureTheory Measure Filter Module`, `open Set Filter MeasureTheory Measure ContinuousLinearMap`, `open scoped Topology Convolution NNReal`, `open Set Filter MeasureTheory Measure Metric`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open Set MeasureTheory Filter`, `open Set MeasureTheory`, `open scoped RealInnerProductSpace`, `open Matrix`, `open scoped RealInnerProductSpace MatrixOrder`, `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal`, `open Filter Set`, `open scoped Topology NNReal`, `open Set Filter MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set Metric`, `open scoped Topology Pointwise NNReal`, `open Metric`):
--
--   ```lean
--   theorem exists_ae_bilipschitz_partition_of_bound
--       (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
--       {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (⊤ : ℝ≥0∞))
--       {A : ℝ≥0} (hA : 0 < A)
--       (hbound : ∀ x ∈ s, ∀ v : E, ‖v‖ ≤ (A : ℝ)*metricSeminorm f x v) :
--       ∃ t : ℕ → Set E,
--         (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
--         Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
--         ∀ i, LipschitzWith K (fun x : t i => f x) ∧
--           AntilipschitzWith (2*A) (fun x : t i => f x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpIntegralFillings.MetricDifferentiation.metricSeminorm` (definitions bundle `OAIQ219IF000` of this split).
--
--   **Used by.** The proof of `OAI.SharpIntegralFillings.EuclideanStraightening.exists_straightened_pieces` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/IntegralFillings/Differentiation/FullRank.lean (declaration OAI.SharpIntegralFillings.MetricDifferentiation.exists_ae_bilipschitz_partition_of_bound)

import Mathlib
import Definitions.Def_OAIQ219IF000

section

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
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_ae_bilipschitz_partition_of_bound
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (⊤ : ℝ≥0∞))
    {A : ℝ≥0} (hA : 0 < A)
    (hbound : ∀ x ∈ s, ∀ v : E, ‖v‖ ≤ (A : ℝ)*metricSeminorm f x v) :
    ∃ t : ℕ → Set E,
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      ∀ i, LipschitzWith K (fun x : t i => f x) ∧
        AntilipschitzWith (2*A) (fun x : t i => f x) := by
  sorry

end SharpIntegralFillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end
