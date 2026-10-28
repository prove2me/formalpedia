-- Prove2me | Theorems.Thm_OAI_CriticalSK_spectralGood_sphere_partition_lower
-- name    : OAI.CriticalSK.spectralGood_sphere_partition_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:22.110996+00:00
-- url     : https://prove2.me/theorems/fbcd7d3e-e12b-4469-ba27-1bd2fd03d924
-- title:
--   OAI.CriticalSK.spectralGood_sphere_partition_lower: intermediate lemma from OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.covariance_and_linear_tests` and `OAI.CriticalSK.critical_mixing_lower_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.spectralGood_sphere_partition_lower` of [lean/OAI/MathematicalPhysics/CriticalSK/PartitionBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/PartitionBounds.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise`, `open Set Metric MeasureTheory MeasureTheory.Measure`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal Topology`, `open MeasureTheory MeasureTheory.Measure Set Metric`, `open scoped NNReal ENNReal BigOperators`, `open scoped NNReal ENNReal`, `open ProbabilityTheory`, `open Metric Set MeasureTheory`, `open scoped ENNReal Pointwise`, `open MeasureTheory Filter Set Real`):
--
--   ```lean
--   lemma spectralGood_sphere_partition_lower {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
--       (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
--       (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
--       (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s)
--       (h0 : |lam 0-2| ≤ s/4) (h1 : |lam 1-2| ≤ s/4) :
--       (s/4)*Real.exp (-6*((n+2:ℝ)*s*Real.sqrt s))*
--         Real.exp ((n+2)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt (n+2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.spectralGood`, `OAI.CriticalSK.spherePartition`, `OAI.CriticalSK.sphericalVariational` and `OAI.CriticalSK.traceCost` (definitions bundle `OAIQWCSK000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalSK.naturalOrientationInputs` of this split imports it.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/PartitionBounds.lean (declaration OAI.CriticalSK.spectralGood_sphere_partition_lower)

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

namespace CriticalSK

lemma spectralGood_sphere_partition_lower {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s)
    (h0 : |lam 0-2| ≤ s/4) (h1 : |lam 1-2| ≤ s/4) :
    (s/4)*Real.exp (-6*((n+2:ℝ)*s*Real.sqrt s))*
      Real.exp ((n+2)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt (n+2)) := by
  sorry

end CriticalSK

end

end OAI
end
