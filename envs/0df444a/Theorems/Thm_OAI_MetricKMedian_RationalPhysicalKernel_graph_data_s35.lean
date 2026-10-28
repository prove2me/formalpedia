-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data_s35
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:45:31.660093+00:00
-- url     : https://prove2.me/theorems/14edb4ba-200e-4e4a-9ea4-d881a64e66b7
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem graph_data_s35 (d : F → F → ℚ) (location : F → X)
--       (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
--       (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
--       (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
--       ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
--         (∀ G, 0 < (graphLaw d g P A).real.weight G → D.Good G) ∧
--         (∀ h i, (graphLaw d g P A).real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
--         (∀ h l i j, i≠j → (graphLaw d g P A).real.expect
--           (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=D.marginal h i*D.marginal l j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy`, `OAI.MetricKMedian.CopyState.own` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.GraphLaw.edge` (definitions bundle `OAIQ035K008` of this split); `OAI.MetricKMedian.Taper.GraphData` and `OAI.MetricKMedian.Taper.GraphData.Good` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.graphLaw` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail_s35`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s35` and `OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s35` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K047

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] in

theorem graph_data_s35 (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
    ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
      (∀ G, 0 < (graphLaw d g P A).real.weight G → D.Good G) ∧
      (∀ h i, (graphLaw d g P A).real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
      (∀ h l i j, i≠j → (graphLaw d g P A).real.expect
        (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=D.marginal h i*D.marginal l j) := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end
