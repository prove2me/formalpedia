-- Prove2me | Theorems.Thm_OAI_SharpIntegralFillings_IntegerChart_exists_scalar_coarea
-- name    : OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T13:34:05.427088+00:00
-- url     : https://prove2.me/theorems/f0e5ef97-0b3e-4ba0-bdeb-22cec3b2a7e7
-- title:
--   OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpIntegralFillings.coefficient_optimal`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea` of [lean/OAI/Geometry/IntegralFillings/Slicing/ScalarCoarea.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/IntegralFillings/Slicing/ScalarCoarea.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpIntegralFillings.IntegerChart`, with `open Set MeasureTheory Measure Filter Module`, `open Set Filter MeasureTheory Measure ContinuousLinearMap`, `open scoped Topology Convolution NNReal`, `open Set Filter MeasureTheory Measure Metric`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open Set MeasureTheory Filter`, `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal`, `open Filter Set`, `open scoped Topology NNReal`, `open Set Filter MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set Metric`, `open scoped Topology Pointwise NNReal`, `open Set MeasureTheory`, `open scoped RealInnerProductSpace`, `open Matrix`, `open scoped RealInnerProductSpace MatrixOrder`, `open Set MeasureTheory Filter`, `open scoped Topology NNReal ENNReal`):
--
--   ```lean
--   theorem exists_scalar_coarea (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0}
--       (hK : LipschitzWith K u) :
--       ∃ (S : ℝ → Functional X k) (G : ℝ → ℝ),
--         Integrable G ∧ (∀ t, 0 ≤ G t) ∧
--         (∀ᵐ t : ℝ, IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t) ∧
--         (∫ t : ℝ, G t) ≤ K * mass C.action ∧
--         (∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
--           C.action b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π) ∧
--         (∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
--           ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpIntegralFillings.IsCAT0` (definitions bundle `OAIQ219IF000` of this split); `OAI.SharpIntegralFillings.Admissible`, `OAI.SharpIntegralFillings.BoundedLip`, `OAI.SharpIntegralFillings.Functional`, `OAI.SharpIntegralFillings.IntegerChart`, `OAI.SharpIntegralFillings.IntegerRectifiable`, `OAI.SharpIntegralFillings.IsMetricCurrent`, `OAI.SharpIntegralFillings.mass` and `OAI.SharpIntegralFillings.IntegerChart.action` (the published bundle `Def_FillingCoefficient`).
--
--   **Used by.** The proof of `OAI.SharpIntegralFillings.coefficient_optimal` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/IntegralFillings/Slicing/ScalarCoarea.lean (declaration OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea)

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
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]

theorem exists_scalar_coarea (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) :
    ∃ (S : ℝ → Functional X k) (G : ℝ → ℝ),
      Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass C.action ∧
      (∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
        C.action b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π) ∧
      (∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
        ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) := by
  sorry

end SharpIntegralFillings.IntegerChart

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

end

end OAI
end
