-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ProducedQueryResources_rank_budget
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:11:39.888674+00:00
-- url     : https://prove2.me/theorems/80130c55-a41d-4d85-95ed-050c19eb8c07
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ProducedQueryResourcesBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ProducedQueryResourcesBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources`, with `open Filter Asymptotic LeafQueryFrontend`, `open scoped Topology`, `open SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--    theorem rank_budget (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
--       (a : Word (problem q k hg).r (problem q k hg).Q)
--       (tail : List (Word (problem q k hg).r (problem q k hg).Q))
--       (haN : (a::tail).Nodup) (haC : ∀z,z∈a::tail) :
--       16*(layoutR (q.input k).freeCount:ℝ)*(L (q.input k).freeCount:ℝ)^2*
--         (rank q k hg a tail:ℝ) ≤ (q.input k).freeCount
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.layoutR` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Input` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.problem` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ProducedQueryResourcesBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget)

import Mathlib
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology
open SubexponentialSAT.MulticolorTypes
noncomputable section

 theorem rank_budget (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀z,z∈a::tail) :
    16*(layoutR (q.input k).freeCount:ℝ)*(L (q.input k).freeCount:ℝ)^2*
      (rank q k hg a tail:ℝ) ≤ (q.input k).freeCount := by
  sorry

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end
