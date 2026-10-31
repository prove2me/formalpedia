-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorProductSpace_accumulate_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:12:21.57989+00:00
-- url     : https://prove2.me/theorems/729d86b5-f692-41b4-8bf8-5991501ce062
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorProductSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorProductSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open SqrtLog SqrtLog.LeafProgram MomentsProgram`):
--
--   ```lean
--   theorem accumulate_run_space (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
--       {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (u J : ℕ) (seed factor : List (Product.Entry n (baseWidth p t) d))
--       (hs : TruncatedRingProgram.Good ∅ u J seed) (hf : TruncatedRingProgram.Good ∅ u J factor) (a : Factor.Data)
--       (hlow : Factor.lowReady a (Product.idle M.bits width cache.zero.val
--         (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
--       (hseed : a.stacks 151 = Product.bytes seed)
--       (hfactor : a.stacks 67 = Product.bytes factor)
--       (h61 : a.stacks 61 = []) (h70 : a.stacks 70 = []) (h159 : a.stacks 159 = []) :
--       let result := Product.run p t M cache table u J seed factor []
--       let program := compiled Factor.accumulate 67 151
--       ∃ steps b, steps ≤ budget n (baseWidth p t) d u J ∧ TruncatedRingProgram.Good ∅ u J result ∧
--         Eval Factor.accumulate steps a b ∧
--         b.stacks = Function.update (Function.update a.stacks 67 []) 151 (Product.bytes result) ∧
--         (Product.bytes result).length ≤ byteBound n (baseWidth p t) d u J ∧
--         Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
--           Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
--           dataBits intermediate ≤ stackBits a.stacks + budget n (baseWidth p t) d u J + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.stackBits` and `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.byteBound` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.dataBits` and `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.budget` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.tableEncoding` (definitions bundle `OAIQ081S101` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.lowReady` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.run` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorProductSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram MomentsProgram

theorem accumulate_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (seed factor : List (Product.Entry n (baseWidth p t) d))
    (hs : TruncatedRingProgram.Good ∅ u J seed) (hf : TruncatedRingProgram.Good ∅ u J factor) (a : Factor.Data)
    (hlow : Factor.lowReady a (Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151 = Product.bytes seed)
    (hfactor : a.stacks 67 = Product.bytes factor)
    (h61 : a.stacks 61 = []) (h70 : a.stacks 70 = []) (h159 : a.stacks 159 = []) :
    let result := Product.run p t M cache table u J seed factor []
    let program := compiled Factor.accumulate 67 151
    ∃ steps b, steps ≤ budget n (baseWidth p t) d u J ∧ TruncatedRingProgram.Good ∅ u J result ∧
      Eval Factor.accumulate steps a b ∧
      b.stacks = Function.update (Function.update a.stacks 67 []) 151 (Product.bytes result) ∧
      (Product.bytes result).length ≤ byteBound n (baseWidth p t) d u J ∧
      Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + budget n (baseWidth p t) d u J + 1 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace
end
