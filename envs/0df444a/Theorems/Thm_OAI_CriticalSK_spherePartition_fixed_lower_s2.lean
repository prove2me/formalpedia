-- Prove2me | Theorems.Thm_OAI_CriticalSK_spherePartition_fixed_lower_s2
-- name    : OAI.CriticalSK.spherePartition_fixed_lower_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:51:16.784442+00:00
-- url     : https://prove2.me/theorems/6ee6bbb3-5363-4a17-ad2c-be552dcb4ef5
-- title:
--   OAI.CriticalSK.spherePartition_fixed_lower_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.spherePartition_fixed_lower` of [lean/OAI/MathematicalPhysics/CriticalSK/PartitionBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/PartitionBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise`, `open Set Metric MeasureTheory MeasureTheory.Measure`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal Topology`, `open MeasureTheory MeasureTheory.Measure Set Metric`, `open scoped NNReal ENNReal BigOperators`, `open scoped NNReal ENNReal`, `open ProbabilityTheory`, `open Metric Set MeasureTheory`, `open scoped ENNReal Pointwise`, `open MeasureTheory Filter Set Real`, `open Set`):
--
--   ```lean
--   lemma spherePartition_fixed_lower_s2 (lam : Fin (n+2) → ℝ) (v : Fin (n+2) → ℝ≥0)
--       {z m d : ℝ} (hv : ∀ i, v i ≠ 0) (hq : ∀ i, (v i:ℝ)⁻¹ = z-lam i)
--       (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1) (hd : 0 < d)
--       (hmean : (∑ i : Fin n, (v i.succ.succ : ℝ)) = (n+2)-d)
--       (hvar : 128*(∑ i : Fin n, (v i.succ.succ : ℝ)^2) ≤ d^2) :
--       Real.pi*gaussianPairPrefactor (v 0) (v 1)*Real.exp (-d/m) *
--         Real.exp ((n+2)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt (n+2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.gaussianPairPrefactor`, `OAI.CriticalSK.spherePartition` and `OAI.CriticalSK.sphericalVariational` (definitions bundle `OAIQ074C000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalSK.spectralGood_orientation_variance_s2` of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/PartitionBounds.lean (declaration OAI.CriticalSK.spherePartition_fixed_lower)

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

namespace CriticalSK

section

open Set

variable {n : ℕ}

lemma spherePartition_fixed_lower_s2 (lam : Fin (n+2) → ℝ) (v : Fin (n+2) → ℝ≥0)
    {z m d : ℝ} (hv : ∀ i, v i ≠ 0) (hq : ∀ i, (v i:ℝ)⁻¹ = z-lam i)
    (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1) (hd : 0 < d)
    (hmean : (∑ i : Fin n, (v i.succ.succ : ℝ)) = (n+2)-d)
    (hvar : 128*(∑ i : Fin n, (v i.succ.succ : ℝ)^2) ≤ d^2) :
    Real.pi*gaussianPairPrefactor (v 0) (v 1)*Real.exp (-d/m) *
      Real.exp ((n+2)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt (n+2)) := by
  sorry

end

end CriticalSK

end

end OAI
end
