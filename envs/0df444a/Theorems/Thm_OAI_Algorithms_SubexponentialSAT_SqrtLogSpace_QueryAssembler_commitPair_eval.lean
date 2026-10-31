-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryAssembler_commitPair_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:16:00.650577+00:00
-- url     : https://prove2.me/theorems/0629c5eb-250b-44a4-b9a8-84c82db8eaa6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryAssembler.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryAssembler.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler`, with `open OAI BitProgram StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram`, `open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor`, `open SubexpLiftRing SubexpQuarticRing`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram`, `open TruncatedRingProgram`):
--
--   ```lean
--   theorem commitPair_eval (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
--       {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
--       (source seed : List (Product.Entry n (baseWidth p t) d))
--       (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
--       (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
--       (a : Data) (B : ℕ)
--       (henv : pairEnvironment a = Squarefree.ScaleProgram.environment p t M cache table minusOne degree width)
--       (hpair : a.stacks 851=Product.bytes source) (hnode : a.stacks 850=Product.bytes seed)
--       (hb : ∀ i,(a.stacks i).length≤ B)
--       (hcapacity : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2)≤ B) :
--       let sign := parity (a.stacks 835) (parity (a.stacks 834) false)
--       let result := signedSum p t M cache table minusOne sign source seed
--       ∃ steps b, Eval commitPair steps a b ∧ Good ∅ u J result ∧
--         b.stacks 850=Product.bytes result ∧ b.stacks 851=[] ∧
--         (∀ i,i∉pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) ∧
--         (∀ i,(b.stacks i).length≤ B) ∧
--         steps+1≤51000*(B+1)+pairUpdateBudget n (baseWidth p t) d u J
--           (a.stacks 834).length (a.stacks 835).length ∧
--         Trace commitPairProgram (steps+1) (a.withPC (some commitPairProgram.entry)) (b.withPC none) ∧
--         ∀ prefixSteps intermediate,prefixSteps≤ steps+1 →
--           Trace commitPairProgram prefixSteps (a.withPC (some commitPairProgram.entry)) intermediate →
--           ∀ i,(intermediate.stacks i).length≤896*B+51000*(B+1)+
--             pairUpdateBudget n (baseWidth p t) d u J (a.stacks 834).length (a.stacks 835).length
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.Environment` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.pairScratch` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.parity` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.pairUpdateBudget` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.environment` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPairProgram` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedSum` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.pairEnvironment` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.commit_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryAssembler.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram

theorem commitPair_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (a : Data) (B : ℕ)
    (henv : pairEnvironment a = Squarefree.ScaleProgram.environment p t M cache table minusOne degree width)
    (hpair : a.stacks 851=Product.bytes source) (hnode : a.stacks 850=Product.bytes seed)
    (hb : ∀ i,(a.stacks i).length≤ B)
    (hcapacity : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2)≤ B) :
    let sign := parity (a.stacks 835) (parity (a.stacks 834) false)
    let result := signedSum p t M cache table minusOne sign source seed
    ∃ steps b, Eval commitPair steps a b ∧ Good ∅ u J result ∧
      b.stacks 850=Product.bytes result ∧ b.stacks 851=[] ∧
      (∀ i,i∉pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length≤ B) ∧
      steps+1≤51000*(B+1)+pairUpdateBudget n (baseWidth p t) d u J
        (a.stacks 834).length (a.stacks 835).length ∧
      Trace commitPairProgram (steps+1) (a.withPC (some commitPairProgram.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps≤ steps+1 →
        Trace commitPairProgram prefixSteps (a.withPC (some commitPairProgram.entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤896*B+51000*(B+1)+
          pairUpdateBudget n (baseWidth p t) d u J (a.stacks 834).length (a.stacks 835).length := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end
