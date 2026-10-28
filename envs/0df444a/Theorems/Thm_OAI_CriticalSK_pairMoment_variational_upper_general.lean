-- Prove2me | Theorems.Thm_OAI_CriticalSK_pairMoment_variational_upper_general
-- name    : OAI.CriticalSK.pairMoment_variational_upper_general
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:02.454419+00:00
-- url     : https://prove2.me/theorems/84822e6a-e81d-420b-b425-2c7371590aca
-- title:
--   OAI.CriticalSK.pairMoment_variational_upper_general: intermediate lemma from OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.covariance_and_linear_tests` and `OAI.CriticalSK.critical_mixing_lower_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.pairMoment_variational_upper_general` of [lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise`, `open Set Metric MeasureTheory MeasureTheory.Measure`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal Topology`, `open MeasureTheory MeasureTheory.Measure Set Metric`, `open scoped NNReal ENNReal BigOperators`, `open scoped NNReal ENNReal`, `open ProbabilityTheory`, `open Metric Set MeasureTheory`, `open scoped ENNReal Pointwise`, `open MeasureTheory Filter Set Real`, `open Finset Real`, `open scoped BigOperators ENNReal Topology`, `open Set MeasureTheory`, `open scoped BigOperators ENNReal`, `open MeasureTheory`, `open Finset Real Filter`, `open scoped Topology`, `open Set MeasureTheory Filter`):
--
--   ```lean
--   lemma pairMoment_variational_upper_general {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n) (lam : Fin n → ℝ)
--       {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n)
--       (hv : ‖v‖ = Real.sqrt n) (horth : inner ℝ u v = 0)
--       (hlam : ∀ i, |lam i| ≤ 3) {q K : ℝ} (hq : |q| ≤ 1) (hK : 0 < K)
--       (hlo : K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n)) :
--       pairMoment lam u v q / spherePartition lam 1 (Real.sqrt n)^2 ≤
--         (26*Real.exp 1*n/K)^2 * Real.exp ((n:ℝ)*saddlePairDeficit lam |q|)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.pairMoment`, `OAI.CriticalSK.saddlePairDeficit`, `OAI.CriticalSK.spherePartition` and `OAI.CriticalSK.sphericalVariational` (definitions bundle `OAIQWCSK000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalSK.orientation_normalized_overlap_bound` of this split imports it.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean (declaration OAI.CriticalSK.pairMoment_variational_upper_general)

import Mathlib
import Definitions.Def_OAIQWCSK000

section

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

lemma pairMoment_variational_upper_general {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n) (lam : Fin n → ℝ)
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
