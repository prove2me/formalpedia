-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafStatisticsProgram_Arity_scopeCall_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:11:31.943547+00:00
-- url     : https://prove2.me/theorems/11cd2c70-e84a-41bf-808c-15f610962f9a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafStatisticsProgramArity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafStatisticsProgramArity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem scopeCall_eval (r : Fin 10 → Bool) (mask source : List Bool) (scope : List ℕ)
--       (hv : ∀ v ∈ scope, v < mask.length) (a q : ℕ) :
--       ∃ n rf, n ≤ 4+RecordPrograms.budget (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat) ∧
--         (∀ i : Fin 10, 7 ≤ i.val → rf i = r i) ∧
--         Eval scopeCall n (state (prepared r) mask (Encoding.encodeList Encoding.encodeNat scope) source [] a q)
--           ⟨rf,Function.update (state r mask [] source [] a q).stacks 4
--             (unary (scope.filter (Scope.low mask)).length)⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.budget` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.low` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.prepared` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.unary` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.state` (definitions bundle `OAIQ081S095` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafStatisticsProgramArity.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S110

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem scopeCall_eval (r : Fin 10 → Bool) (mask source : List Bool) (scope : List ℕ)
    (hv : ∀ v ∈ scope, v < mask.length) (a q : ℕ) :
    ∃ n rf, n ≤ 4+RecordPrograms.budget (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = r i) ∧
      Eval scopeCall n (state (prepared r) mask (Encoding.encodeList Encoding.encodeNat scope) source [] a q)
        ⟨rf,Function.update (state r mask [] source [] a q).stacks 4
          (unary (scope.filter (Scope.low mask)).length)⟩ := by
  sorry

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end
