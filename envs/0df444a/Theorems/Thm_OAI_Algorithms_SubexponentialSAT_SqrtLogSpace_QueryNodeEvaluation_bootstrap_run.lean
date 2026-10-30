-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_bootstrap_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:33:21.075695+00:00
-- url     : https://prove2.me/theorems/228b6173-4cfc-4a7f-a909-0b95d66d334e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage`, `open LeafHeadSetupProgram QueryTupleState`):
--
--   ```lean
--   theorem bootstrap_run (s : Native.Inputs) (a : Data) (B : ℕ)
--       (ha : Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a))
--       (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B)
--       (h710 : a.stacks 710=[]) (h711 : a.stacks 711=[]) (h712 : a.stacks 712=[]) :
--       ∃ ra rd rc words ticks,
--         CacheCorrect s.height (unary s.R) s.width words ∧
--         ticks ≤ 20000*(B+1)^4+1 ∧
--         Eval QueryStreamProgram.bootstrapNode ticks a (bootstrapped s a ra rd rc words) ∧
--         WordBound B (bootstrapped s a ra rd rc words)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.Nodes.lowPort` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.bootstrapOutputBound` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.bootstrapNode` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.Data` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrapped` (definitions bundle `OAIQ081S185` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S185

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

theorem bootstrap_run (s : Native.Inputs) (a : Data) (B : ℕ)
    (ha : Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a))
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B)
    (h710 : a.stacks 710=[]) (h711 : a.stacks 711=[]) (h712 : a.stacks 712=[]) :
    ∃ ra rd rc words ticks,
      CacheCorrect s.height (unary s.R) s.width words ∧
      ticks ≤ 20000*(B+1)^4+1 ∧
      Eval QueryStreamProgram.bootstrapNode ticks a (bootstrapped s a ra rd rc words) ∧
      WordBound B (bootstrapped s a ra rd rc words) := by
  sorry

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end
