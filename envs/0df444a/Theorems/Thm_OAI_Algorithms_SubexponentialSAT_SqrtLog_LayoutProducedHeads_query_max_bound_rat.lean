-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_query_max_bound_rat
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:43:21.721451+00:00
-- url     : https://prove2.me/theorems/cc456c3a-d27e-4ff3-82f0-68d32c1bfbcd
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsQuery.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsQuery.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads`, with `open SubexponentialSAT.MulticolorTypes LeafParametersProgram LeafQueryFrontend`):
--
--   ```lean
--   theorem query_max_bound_rat (q : Query) (k : ℕ) (hg : Guard (q.input k))
--       (a : Word (LeafProgram.Query.packingProblem q k hg).r
--         (LeafProgram.Query.packingProblem q k hg).Q)
--       (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
--         (LeafProgram.Query.packingProblem q k hg).Q))
--       (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
--       let p := LeafProgram.Query.packingProblem q k hg
--       (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
--         (q.forward.map Bool.not) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan.encodeWord` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.maxSelected` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.words` (definitions bundle `OAIQ081S089` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.forward` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.packingProblem` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsQuery.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat)

import Mathlib
import Definitions.Def_OAIQ081S168

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open SubexponentialSAT.MulticolorTypes LeafParametersProgram LeafQueryFrontend

theorem query_max_bound_rat (q : Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    let p := LeafProgram.Query.packingProblem q k hg
    (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end

end OAI.Algorithms
end
