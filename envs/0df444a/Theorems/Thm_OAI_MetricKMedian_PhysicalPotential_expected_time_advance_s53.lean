-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PhysicalPotential_expected_time_advance_s53
-- name    : OAI.MetricKMedian.PhysicalPotential.expected_time_advance_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:36:16.263676+00:00
-- url     : https://prove2.me/theorems/b4df77b8-5237-4f5f-868c-bc24a706bf31
-- title:
--   OAI.MetricKMedian.PhysicalPotential.expected_time_advance_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PhysicalPotential.expected_time_advance` of [lean/OAI/Combinatorics/KMedian/Process/PhaseBatchBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/PhaseBatchBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PhysicalPotential`, with `open Analytic`):
--
--   ```lean
--   theorem expected_time_advance_s53 (μ : FiniteLaw Ω) (S' : Ω → Finset I) (b' : Ω → ℝ)
--       {x g R h : ℝ} (d : I → ℝ) (S : Finset I)
--       (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R) (hh : 0 ≤ h)
--       (hd0 : ∀ i ∈ S, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
--       (hy : mass g S ≤ 1) (hsub : ∀ ω, S' ω ⊆ S) :
--       μ.expect (fun ω => potential (x*Real.exp (-h)) g d (S' ω) (b' ω)-
--         potential x g d (S' ω) (b' ω)) ≤
--         h*timeRate x (mass g S)*cost g d S+6*h^2*R+
--           4*h*R*μ.prob (fun ω => S' ω ≠ S)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.timeRate` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.FiniteLaw` and `OAI.MetricKMedian.FiniteLaw.expect` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ053K007` of this split); `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ053K020` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/PhaseBatchBound.lean (declaration OAI.MetricKMedian.PhysicalPotential.expected_time_advance)

import Mathlib
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K020

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic
variable {I Ω : Type*} [DecidableEq I] [Fintype Ω]

theorem expected_time_advance_s53 (μ : FiniteLaw Ω) (S' : Ω → Finset I) (b' : Ω → ℝ)
    {x g R h : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R) (hh : 0 ≤ h)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hsub : ∀ ω, S' ω ⊆ S) :
    μ.expect (fun ω => potential (x*Real.exp (-h)) g d (S' ω) (b' ω)-
      potential x g d (S' ω) (b' ω)) ≤
      h*timeRate x (mass g S)*cost g d S+6*h^2*R+
        4*h*R*μ.prob (fun ω => S' ω ≠ S) := by
  sorry

end MetricKMedian.PhysicalPotential

end
end

end OAI
end
