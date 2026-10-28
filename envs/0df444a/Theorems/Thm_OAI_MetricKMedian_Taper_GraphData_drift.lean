-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Taper_GraphData_drift
-- name    : OAI.MetricKMedian.Taper.GraphData.drift
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-27T08:26:14.138964+00:00
-- url     : https://prove2.me/theorems/2bf6b1e2-f0f9-469d-bb30-70c1a07f9760
-- title:
--   OAI.MetricKMedian.Taper.GraphData.drift: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Taper`, with `open Finset`):
--
--   ```lean
--   theorem GraphData.drift {Δ : ℕ} {g P x ζ b : ℝ} {location : I → X} {own : I → Finset I}
--       (D : GraphData Δ g P location own) (μ : FiniteLaw (I → Finset I))
--       (client : X) (S : Finset I)
--       (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (hP : 0 ≤ P) (hP1 : P ≤ 1/2)
--       (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : PhysicalPotential.mass g S ≤ 1)
--       (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |P-Analytic.P x| ≤ ζ)
--       (hfirst : ∀ h i, μ.expect (fun G => GraphLaw.edge G h i)=D.marginal h i)
--       (hpair : ∀ h k i j, i ≠ j → μ.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G k j)=
--         D.marginal h i*D.marginal k j) :
--       Analytic.timeRate x (PhysicalPotential.mass g S)*
--           PhysicalPotential.cost g (fun i => dist client (location i)) S+
--         μ.expect (fun G => g*∑ h ∈ FixedBatch.relevant (FixedBatch.graphActions G) S,
--           FixedBatch.charge (FixedBatch.graphActions G) x g b
--             (fun i => dist client (location i)) S h) ≤
--         Analytic.B x*g*PhysicalPotential.cost g (fun i => dist client (location i)) S+
--           12*ζ*PhysicalPotential.cost g (fun i => dist client (location i)) S
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.B`, `OAI.MetricKMedian.Analytic.P` and `OAI.MetricKMedian.Analytic.timeRate` (definitions bundle `OAIQ035K000` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.expect`, `OAI.MetricKMedian.FixedBatch.graphActions` and `OAI.MetricKMedian.FixedBatch.relevant` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ035K007` of this split); `OAI.MetricKMedian.GraphLaw.edge` (definitions bundle `OAIQ035K008` of this split); `OAI.MetricKMedian.Taper.GraphData` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.FixedBatch.charge` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.step_drift` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I X : Type*} [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

theorem GraphData.drift {Δ : ℕ} {g P x ζ b : ℝ} {location : I → X} {own : I → Finset I}
    (D : GraphData Δ g P location own) (μ : FiniteLaw (I → Finset I))
    (client : X) (S : Finset I)
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (hP : 0 ≤ P) (hP1 : P ≤ 1/2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : PhysicalPotential.mass g S ≤ 1)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |P-Analytic.P x| ≤ ζ)
    (hfirst : ∀ h i, μ.expect (fun G => GraphLaw.edge G h i)=D.marginal h i)
    (hpair : ∀ h k i j, i ≠ j → μ.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G k j)=
      D.marginal h i*D.marginal k j) :
    Analytic.timeRate x (PhysicalPotential.mass g S)*
        PhysicalPotential.cost g (fun i => dist client (location i)) S+
      μ.expect (fun G => g*∑ h ∈ FixedBatch.relevant (FixedBatch.graphActions G) S,
        FixedBatch.charge (FixedBatch.graphActions G) x g b
          (fun i => dist client (location i)) S h) ≤
      Analytic.B x*g*PhysicalPotential.cost g (fun i => dist client (location i)) S+
        12*ζ*PhysicalPotential.cost g (fun i => dist client (location i)) S := by
  sorry

end MetricKMedian.Taper
end
end

end OAI
end
