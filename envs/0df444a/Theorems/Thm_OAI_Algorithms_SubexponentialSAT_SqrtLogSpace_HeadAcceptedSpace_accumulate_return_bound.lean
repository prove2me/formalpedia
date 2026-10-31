-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadAcceptedSpace_accumulate_return_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.accumulate_return_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:16:38.550288+00:00
-- url     : https://prove2.me/theorems/f6f5edbc-e057-47c0-80b4-b6e2ebc9afed
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.accumulate_return_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.accumulate_return_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace`, with `open BitProgram StructuredCalls HighQueryAdapter`, `open CounterPrograms CounterForPrograms`, `open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram`, `open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram`):
--
--   ```lean
--   theorem accumulate_return_bound (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {n d u J steps inputCap : ℕ}
--       (source seed : List (Product.Entry n (baseWidth p t) d))
--       (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
--       (a e : HeadSumProgram.Data) (width degree zero table uCap zCap : List Bool)
--       (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
--         Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i)
--       (hseedWord : a.stacks 853 = Product.bytes seed)
--       (hsourceWord : a.stacks 854 = Product.bytes source)
--       (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = [])
--       (harray : u * J * (2 * (u + J + n) + 2 * (d * baseWidth p t) + 2) ≤ inputCap)
--       (hinput : ∀ i, (a.stacks i).length ≤ inputCap)
--       (he : Eval accumulate steps a e) :
--       ∀ i, (e.stacks i).length ≤ inputCap
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.tapes` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.accumulate_return_bound)

import Mathlib
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace

open BitProgram StructuredCalls HighQueryAdapter

open CounterPrograms CounterForPrograms

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram

theorem accumulate_return_bound (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J steps inputCap : ℕ}
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a e : HeadSumProgram.Data) (width degree zero table uCap zCap : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i)
    (hseedWord : a.stacks 853 = Product.bytes seed)
    (hsourceWord : a.stacks 854 = Product.bytes source)
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = [])
    (harray : u * J * (2 * (u + J + n) + 2 * (d * baseWidth p t) + 2) ≤ inputCap)
    (hinput : ∀ i, (a.stacks i).length ≤ inputCap)
    (he : Eval accumulate steps a e) :
    ∀ i, (e.stacks i).length ≤ inputCap := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace
end
