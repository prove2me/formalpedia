-- Prove2me | Theorems.Thm_OAI_CriticalSK_spectralGood_saddle_uniform
-- name    : OAI.CriticalSK.spectralGood_saddle_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:20.096901+00:00
-- url     : https://prove2.me/theorems/52adb473-1008-4440-b718-fcf80f124467
-- title:
--   OAI.CriticalSK.spectralGood_saddle_uniform: intermediate lemma from OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.covariance_and_linear_tests` and `OAI.CriticalSK.critical_mixing_lower_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.spectralGood_saddle_uniform` of [lean/OAI/MathematicalPhysics/CriticalSK/SaddleLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/SaddleLimit.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise`, `open Set Metric MeasureTheory MeasureTheory.Measure`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal Topology`, `open MeasureTheory MeasureTheory.Measure Set Metric`, `open scoped NNReal ENNReal BigOperators`, `open scoped NNReal ENNReal`, `open ProbabilityTheory`, `open Metric Set MeasureTheory`, `open scoped ENNReal Pointwise`, `open MeasureTheory Filter Set Real`, `open Set Filter`):
--
--   ```lean
--   lemma spectralGood_saddle_uniform {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
--       (hcost : edgeFixedCost h L < 1/100) (hspace : 16 ≤ L*Real.sqrt L)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood n h (naturalEdgeScale n L),
--         saddleSubcriticalError lam+naturalEdgeScale n L/2 < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.edgeFixedCost`, `OAI.CriticalSK.naturalEdgeScale`, `OAI.CriticalSK.saddleSubcriticalError` and `OAI.CriticalSK.spectralGood` (definitions bundle `OAIQWCSK000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalSK.naturalOrientationInputs` of this split imports it.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/SaddleLimit.lean (declaration OAI.CriticalSK.spectralGood_saddle_uniform)

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

open Set Filter

lemma spectralGood_saddle_uniform {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (hspace : 16 ≤ L*Real.sqrt L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood n h (naturalEdgeScale n L),
      saddleSubcriticalError lam+naturalEdgeScale n L/2 < ε := by
  sorry

end CriticalSK

end

end OAI
end
