-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Reduction_completion_branch_exists_s53
-- name    : OAI.MetricKMedian.Reduction.completion_branch_exists_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:37:53.222803+00:00
-- url     : https://prove2.me/theorems/ba3743fc-eac9-4ccc-9566-e0c1c7c369ef
-- title:
--   OAI.MetricKMedian.Reduction.completion_branch_exists_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Reduction.completion_branch_exists` of [lean/OAI/Combinatorics/KMedian/Reduction/CompletionEnumeration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/CompletionEnumeration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Reduction`, with `open Finset`):
--
--   ```lean
--   theorem completion_branch_exists_s53 (F O U : Finset (Fin I.n)) (hOF : O ⊆ F)
--       (hO : O.Nonempty) (hk : O.card=I.k) (hUF : U ⊆ F) (hU : I.k < U.card)
--       (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
--       (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
--       (hcost : cost I U ≤ α*cost I O)
--       (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
--       (hstuck : ∀ i ∈ U, η*cost I O/c ≤ cost I (U.erase i)-cost I U)
--       (hb : 6*α*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
--       ∃ S ∈ completionBranches I F U δ b,
--         S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (1+12*(δ:ℝ))*cost I O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Reduction.Sparse` (definitions bundle `OAIQ053K027` of this split); `OAI.MetricKMedian.Reduction.completionBranches` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.Instance` and `OAI.MetricKMedian.cost` (the published bundle `Def_KMedianThreshold`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Reduction.reductionOutputs_success_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/CompletionEnumeration.lean (declaration OAI.MetricKMedian.Reduction.completion_branch_exists)

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K037

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

local instance completionEnumerationPseudoMetric_rc70a09_1 : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
theorem completion_branch_exists_s53 (F O U : Finset (Fin I.n)) (hOF : O ⊆ F)
    (hO : O.Nonempty) (hk : O.card=I.k) (hUF : U ⊆ F) (hU : I.k < U.card)
    (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
    (hcost : cost I U ≤ α*cost I O)
    (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
    (hstuck : ∀ i ∈ U, η*cost I O/c ≤ cost I (U.erase i)-cost I U)
    (hb : 6*α*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
    ∃ S ∈ completionBranches I F U δ b,
      S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (1+12*(δ:ℝ))*cost I O := by
  sorry

end MetricKMedian.Reduction
end
end

end OAI
end
