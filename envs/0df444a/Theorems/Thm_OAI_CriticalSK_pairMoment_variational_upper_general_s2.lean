-- Prove2me | Theorems.Thm_OAI_CriticalSK_pairMoment_variational_upper_general_s2
-- name    : OAI.CriticalSK.pairMoment_variational_upper_general_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:50:41.007921+00:00
-- url     : https://prove2.me/theorems/b6ba25a2-a414-4388-a55e-2132ae3c85d8
-- title:
--   OAI.CriticalSK.pairMoment_variational_upper_general_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.pairMoment_variational_upper_general` of [lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise`, `open Set Metric MeasureTheory MeasureTheory.Measure`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal Topology`, `open MeasureTheory MeasureTheory.Measure Set Metric`, `open scoped NNReal ENNReal BigOperators`, `open scoped NNReal ENNReal`, `open ProbabilityTheory`, `open Metric Set MeasureTheory`, `open scoped ENNReal Pointwise`, `open MeasureTheory Filter Set Real`, `open Finset Real`, `open scoped BigOperators ENNReal Topology`, `open Set MeasureTheory`, `open scoped BigOperators ENNReal`, `open MeasureTheory`, `open Finset Real Filter`, `open scoped Topology`, `open Set MeasureTheory Filter`):
--
--   ```lean
--   lemma pairMoment_variational_upper_general_s2 {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n) (lam : Fin n → ℝ)
--       {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n)
--       (hv : ‖v‖ = Real.sqrt n) (horth : inner ℝ u v = 0)
--       (hlam : ∀ i, |lam i| ≤ 3) {q K : ℝ} (hq : |q| ≤ 1) (hK : 0 < K)
--       (hlo : K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n)) :
--       pairMoment lam u v q / spherePartition lam 1 (Real.sqrt n)^2 ≤
--         (26*Real.exp 1*n/K)^2 * Real.exp ((n:ℝ)*saddlePairDeficit lam |q|)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.pairMoment`, `OAI.CriticalSK.saddlePairDeficit`, `OAI.CriticalSK.spherePartition` and `OAI.CriticalSK.sphericalVariational` (definitions bundle `OAIQ074C000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalSK.orientation_normalized_variance_bound_s2` of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean (declaration OAI.CriticalSK.pairMoment_variational_upper_general)

import Mathlib
import Definitions.Def_OAIQ074C000

section

attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

open Set MeasureTheory Filter

lemma pairMoment_variational_upper_general_s2 {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n) (lam : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n)
    (hv : ‖v‖ = Real.sqrt n) (horth : inner ℝ u v = 0)
    (hlam : ∀ i, |lam i| ≤ 3) {q K : ℝ} (hq : |q| ≤ 1) (hK : 0 < K)
    (hlo : K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n)) :
    pairMoment lam u v q / spherePartition lam 1 (Real.sqrt n)^2 ≤
      (26*Real.exp 1*n/K)^2 * Real.exp ((n:ℝ)*saddlePairDeficit lam |q|) := by
  sorry

end CriticalSK

end

end OAI
end
