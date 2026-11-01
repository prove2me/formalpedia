-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_graph_data_all_s53
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:41:20.841344+00:00
-- url     : https://prove2.me/theorems/6160287b-d8a7-4170-8255-3e2e7ee5b593
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all` of [lean/OAI/Combinatorics/KMedian/Geometry/RationalHistoryValid.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Geometry/RationalHistoryValid.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem graph_data_all_s53 (d : F → F → ℚ) (location : F → X)
--       (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
--       (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
--       (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
--       ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
--         ∀ a : Fin (graphLaw d g P A).length, D.Good (graphLaw d g P A).states[a.val]
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.CopyState.own` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.Taper.GraphData` and `OAI.MetricKMedian.Taper.GraphData.Good` (definitions bundle `OAIQ053K012` of this split); `OAI.MetricKMedian.SparseIntegerLaw` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.graphLaw` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Geometry/RationalHistoryValid.lean (declaration OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all)

import Mathlib
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
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}

local instance rationalHistoryValidCopyOrder_r0e6c5a_1 : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder
omit [Fintype F] [Fintype J] [DecidableEq J] in

theorem graph_data_all_s53 (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
    ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
      ∀ a : Fin (graphLaw d g P A).length, D.Good (graphLaw d g P A).states[a.val] := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end
