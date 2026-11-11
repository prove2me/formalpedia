-- Prove2me | Theorems.Thm_OAI_SharpIntegralFillings_EuclideanStraightening_exists_straightened_pieces
-- name    : OAI.SharpIntegralFillings.EuclideanStraightening.exists_straightened_pieces
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T13:35:43.690941+00:00
-- url     : https://prove2.me/theorems/1058bac8-acc2-4100-bb6a-6c97300edd8d
-- title:
--   OAI.SharpIntegralFillings.EuclideanStraightening.exists_straightened_pieces: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpIntegralFillings.coefficient_optimal`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpIntegralFillings.EuclideanStraightening.exists_straightened_pieces` of [lean/OAI/Geometry/IntegralFillings/Charts/StraightPieces.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/IntegralFillings/Charts/StraightPieces.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpIntegralFillings.EuclideanStraightening`, with `open Set MeasureTheory Measure Filter Module`, `open Set Filter MeasureTheory Measure ContinuousLinearMap`, `open scoped Topology Convolution NNReal`, `open Set Filter MeasureTheory Measure Metric`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open Set MeasureTheory Filter`, `open Set MeasureTheory`, `open scoped RealInnerProductSpace`, `open Matrix`, `open scoped RealInnerProductSpace MatrixOrder`, `open Set Filter MeasureTheory`, `open scoped Topology ENNReal NNReal`, `open Filter Set`, `open scoped Topology NNReal`, `open Set Filter MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set Metric`, `open scoped Topology Pointwise NNReal`, `open Set MeasureTheory Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   theorem exists_straightened_pieces {k : ℕ} {s : Set (Euc (k+1))}
--       (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
--       {g : Euc (k+1) → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
--       ∃ (t : ℕ → Set (Euc (k+1))) (dir : ℕ → Fin (k+1)) (J : ℕ → ℝ≥0),
--         (∀ i, t i ⊆ s) ∧ (∀ i, MeasurableSet (t i)) ∧
--         Pairwise (fun i l => Disjoint (t i) (t l)) ∧
--         (∀ i, LipschitzWith (1+K+‖(EuclideanSpace.proj (dir i) : Euc (k+1) →L[ℝ] ℝ)‖₊)
--             (fun x : t i => straightenMap (dir i) g x) ∧
--           AntilipschitzWith (J i) (fun x : t i => straightenMap (dir i) g x)) ∧
--         ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i → fderiv ℝ g x = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap` (definitions bundle `OAIQ219IF000` of this split); `OAI.SharpIntegralFillings.Euc` (the published bundle `Def_FillingCoefficient`).
--
--   **Used by.** The proof of `OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/IntegralFillings/Charts/StraightPieces.lean (declaration OAI.SharpIntegralFillings.EuclideanStraightening.exists_straightened_pieces)

import Mathlib
import Definitions.Def_FillingCoefficient
import Definitions.Def_OAIQ219IF000

section

attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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

namespace SharpIntegralFillings.EuclideanStraightening
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem exists_straightened_pieces {k : ℕ} {s : Set (Euc (k+1))}
    (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
    {g : Euc (k+1) → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∃ (t : ℕ → Set (Euc (k+1))) (dir : ℕ → Fin (k+1)) (J : ℕ → ℝ≥0),
      (∀ i, t i ⊆ s) ∧ (∀ i, MeasurableSet (t i)) ∧
      Pairwise (fun i l => Disjoint (t i) (t l)) ∧
      (∀ i, LipschitzWith (1+K+‖(EuclideanSpace.proj (dir i) : Euc (k+1) →L[ℝ] ℝ)‖₊)
          (fun x : t i => straightenMap (dir i) g x) ∧
        AntilipschitzWith (J i) (fun x : t i => straightenMap (dir i) g x)) ∧
      ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i → fderiv ℝ g x = 0 := by
  sorry

end SharpIntegralFillings.EuclideanStraightening
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
