-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_marked_tail_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:28:04.439774+00:00
-- url     : https://prove2.me/theorems/111b07a6-b07f-411b-b751-37bda0174a9f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorFinish.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorFinish.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open HashCircuitProgram.Native`):
--
--   ```lean
--   theorem marked_tail_eval (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
--       (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
--       (u J : ℕ) (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
--       (a : Data)
--       (hlo : lowReady a (MomentsProgram.Product.idle M.bits width cache.zero.val
--         (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
--       (hseed : a.stacks 151=MomentsProgram.Product.bytes seed)
--       (hfactor : a.stacks 67=MomentsProgram.Product.bytes factor)
--       (h61 : a.stacks 61=[]) (h70 : a.stacks 70=[]) (h159 : a.stacks 159=[]) :
--       let result := MomentsProgram.Product.run p t M cache table u J seed factor []
--       ∃ k b, k ≤ 2*(a.stacks 62).length+3+productBudget p t M cache table u J seed factor ∧
--         Eval (.seq (clear 62) accumulate) k a b ∧
--         b.stacks=Function.update (Function.update (Function.update a.stacks 62 []) 67 [])
--           151 (MomentsProgram.Product.bytes result)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.clear` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.tableEncoding` (definitions bundle `OAIQ081S101` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.lowReady` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.run` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.productBudget` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorFinish.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native

theorem marked_tail_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (u J : ℕ) (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (a : Data)
    (hlo : lowReady a (MomentsProgram.Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151=MomentsProgram.Product.bytes seed)
    (hfactor : a.stacks 67=MomentsProgram.Product.bytes factor)
    (h61 : a.stacks 61=[]) (h70 : a.stacks 70=[]) (h159 : a.stacks 159=[]) :
    let result := MomentsProgram.Product.run p t M cache table u J seed factor []
    ∃ k b, k ≤ 2*(a.stacks 62).length+3+productBudget p t M cache table u J seed factor ∧
      Eval (.seq (clear 62) accumulate) k a b ∧
      b.stacks=Function.update (Function.update (Function.update a.stacks 62 []) 67 [])
        151 (MomentsProgram.Product.bytes result) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end
