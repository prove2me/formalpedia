-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumProgram_accumulate_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:16:36.17889+00:00
-- url     : https://prove2.me/theorems/161fc06e-d9a9-4cb6-b6aa-c96361162128
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram`, with `open OAI BitProgram StructuredCalls CounterPrograms`, `open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing`, `open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram`):
--
--   ```lean
--   theorem accumulate_eval (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
--       (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
--       (a : Data) (width degree zero table uCap zCap : List Bool)
--       (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
--         Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i)
--       (hseedWord : a.stacks 853 = Product.bytes seed)
--       (hsourceWord : a.stacks 854 = Product.bytes source)
--       (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = []) :
--       let result := Normalize.run p t M cache source seed
--       let budget := additionBudget n (baseWidth p t) d u J + FactorEnvironment.resetCost a
--       ∃ steps e, steps ≤ budget ∧ Eval accumulate steps a e ∧ Good ∅ u J result ∧
--         e.stacks = Function.update (Function.update (FactorEnvironment.resetResult a).stacks
--           853 (Product.bytes result)) 854 [] ∧
--         (∀ i : Fin 56, e.stacks (Fin.castAdd 840 i) = []) ∧
--         ∀ q z, q ≤ steps + 1 → Trace (compiled accumulate 854 853) q
--           (a.withPC (some (compiled accumulate 854 853).entry)) z →
--           dataBits z ≤ stackBits a.stacks + budget + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.stackBits` and `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.tapes` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.dataBits` and `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.additionBudget` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.resetCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.resetResult` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.accumulate_return_bound` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval)

import Mathlib
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram

theorem accumulate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a : Data) (width degree zero table uCap zCap : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i)
    (hseedWord : a.stacks 853 = Product.bytes seed)
    (hsourceWord : a.stacks 854 = Product.bytes source)
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = []) :
    let result := Normalize.run p t M cache source seed
    let budget := additionBudget n (baseWidth p t) d u J + FactorEnvironment.resetCost a
    ∃ steps e, steps ≤ budget ∧ Eval accumulate steps a e ∧ Good ∅ u J result ∧
      e.stacks = Function.update (Function.update (FactorEnvironment.resetResult a).stacks
        853 (Product.bytes result)) 854 [] ∧
      (∀ i : Fin 56, e.stacks (Fin.castAdd 840 i) = []) ∧
      ∀ q z, q ≤ steps + 1 → Trace (compiled accumulate 854 853) q
        (a.withPC (some (compiled accumulate 854 853).entry)) z →
        dataBits z ≤ stackBits a.stacks + budget + 1 := by
  sorry

open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end
