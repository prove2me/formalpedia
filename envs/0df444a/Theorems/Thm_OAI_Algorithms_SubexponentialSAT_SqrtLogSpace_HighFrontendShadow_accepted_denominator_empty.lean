-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighFrontendShadow_accepted_denominator_empty
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:28:46.694042+00:00
-- url     : https://prove2.me/theorems/05a2aa6d-4e85-4f86-a790-daeddec26048
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighFrontendShadow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighFrontendShadow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow`, with `open BitProgram StructuredCalls SqrtLog HighMarkedFrontend`):
--
--   ```lean
--   theorem accepted_denominator_empty (q : LeafQueryFrontend.Query) (k : ℕ)
--       (a b : Data) (steps : ℕ) (hv : q.Valid)
--       (hc : LeafProgram.Query.CleanWork (project a))
--       (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark = none)
--       (hindex : q.index = [false]) (he : Eval (acceptedCommand k) steps a b) :
--       b.stacks 728 = []
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.CleanWork` (definitions bundle `OAIQ081S127` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Sources` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedCommand` (definitions bundle `OAIQ081S183` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighFrontendShadow.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S183

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow

open BitProgram StructuredCalls SqrtLog HighMarkedFrontend

theorem accepted_denominator_empty (q : LeafQueryFrontend.Query) (k : ℕ)
    (a b : Data) (steps : ℕ) (hv : q.Valid)
    (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark = none)
    (hindex : q.index = [false]) (he : Eval (acceptedCommand k) steps a b) :
    b.stacks 728 = [] := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow
end
