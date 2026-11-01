-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data_s53
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:40:56.09784+00:00
-- url     : https://prove2.me/theorems/1a3c1137-f9b8-4e09-b571-d866092b4a96
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.RationalPhysicalKernel.graph_data` of [lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalGraphInstance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalGraphInstance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem graph_data_s53 (d : F → F → ℚ) (location : F → X)
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
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.CopyState.own` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.GraphLaw.edge` (definitions bundle `OAIQ053K007` of this split); `OAI.MetricKMedian.Taper.GraphData` and `OAI.MetricKMedian.Taper.GraphData.Good` (definitions bundle `OAIQ053K012` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.graphLaw` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53` and `OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalPhysicalGraphInstance.lean (declaration OAI.MetricKMedian.RationalPhysicalKernel.graph_data)

import Mathlib
import Definitions.Def_OAIQ053K007
import Definitions.Def_OAIQ053K012
import Definitions.Def_OAIQ053K039

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
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

local instance instLinearOrderCopy_1_r1ba2a8_1 : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder
omit [Fintype F] in

theorem graph_data_s53 (d : F → F → ℚ) (location : F → X)
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
