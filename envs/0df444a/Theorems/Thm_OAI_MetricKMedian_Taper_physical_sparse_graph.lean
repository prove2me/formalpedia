-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Taper_physical_sparse_graph
-- name    : OAI.MetricKMedian.Taper.physical_sparse_graph
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:38:04.880356+00:00
-- url     : https://prove2.me/theorems/a6117b70-d12a-4367-a96f-6992e6af0d77
-- title:
--   OAI.MetricKMedian.Taper.physical_sparse_graph: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Taper`, with `open Finset`):
--
--   ```lean
--   theorem physical_sparse_graph (enum : Fin n ≃ I) (Δ : ℕ) (g P : ℚ)
--       (d : I → I → ℚ) (location : I → X) (own : I → Finset I)
--       (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
--       (hd : ∀ i h, 0 ≤ d i h) (hdist : ∀ i h, dist (location i) (location h)=(d i h:ℝ))
--       (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
--       (hown : ∀ i h, h∈own i → d i h=0) (howncard : ∀ i, (own i).card ≤ Δ) :
--       let D := physicalGraphData Δ g P d location own hg hunit hP hP1 hd hdist htotal hown howncard
--       let q := fun h i => sourceMarginals g P (d i) (own i) Δ h
--       let μ := SparseEnumeratedGraph.law enum q
--       μ.length ≤ n*n+(n*n)*(n*n)+1 ∧
--         (∀ G, 0 < μ.real.weight G → D.Good G) ∧
--         (∀ h i, μ.real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
--         (∀ h l i j, i≠j → μ.real.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=
--           D.marginal h i*D.marginal l j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.GraphLaw.edge` (definitions bundle `OAIQ035K008` of this split); `OAI.MetricKMedian.Taper.GraphData` and `OAI.MetricKMedian.Taper.GraphData.Good` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.SparseIntegerLaw` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.Taper.sourceMarginals` (definitions bundle `OAIQ035K019` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.Taper.physicalGraphData` (definitions bundle `OAIQ035K045` of this split); `OAI.MetricKMedian.SparseEnumeratedGraph.law` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.graph_data` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047

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
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ} {X : Type*} [PseudoMetricSpace X]

theorem physical_sparse_graph (enum : Fin n ≃ I) (Δ : ℕ) (g P : ℚ)
    (d : I → I → ℚ) (location : I → X) (own : I → Finset I)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i h, 0 ≤ d i h) (hdist : ∀ i h, dist (location i) (location h)=(d i h:ℝ))
    (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hown : ∀ i h, h∈own i → d i h=0) (howncard : ∀ i, (own i).card ≤ Δ) :
    let D := physicalGraphData Δ g P d location own hg hunit hP hP1 hd hdist htotal hown howncard
    let q := fun h i => sourceMarginals g P (d i) (own i) Δ h
    let μ := SparseEnumeratedGraph.law enum q
    μ.length ≤ n*n+(n*n)*(n*n)+1 ∧
      (∀ G, 0 < μ.real.weight G → D.Good G) ∧
      (∀ h i, μ.real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
      (∀ h l i j, i≠j → μ.real.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=
        D.marginal h i*D.marginal l j) := by
  sorry

end MetricKMedian.Taper
end
end

end OAI
end
