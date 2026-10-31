-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryProgram_signedScale_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:18:48.384813+00:00
-- url     : https://prove2.me/theorems/c550f074-d70d-4945-b856-d504df9377ad
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram`, with `open OAI BitProgram`, `open scoped BigOperators`, `open StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram TruncatedRingProgram`):
--
--   ```lean
--   theorem signedScale_run_space (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
--       {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
--       (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good ∅ u J a)
--       (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (regs : Fin 8 → Bool) (sign : Bool) :
--       let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
--       let start := (signedState regs (Squarefree.ScaleProgram.idle e (Product.bytes a) []) sign).withPC
--         (some signedScaleProgram.entry)
--       let result := signedEntries p t M cache table minusOne sign a
--       ∃ steps rr, steps ≤ signedScalingBudget n (baseWidth p t) d u J ∧
--         Trace signedScaleProgram steps start
--           ((signedState rr {Squarefree.ScaleProgram.idle e [] [] with
--             output := Product.bytes result} sign).withPC none) ∧ Good ∅ u J result ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ steps →
--           Trace signedScaleProgram prefixSteps start intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             dataBits start + signedScalingBudget n (baseWidth p t) d u J
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.Environment` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScalingBudget` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.dataBits` and `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.Store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.idle` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScaleProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.environment` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedEntries` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedState` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

open StructuredCalls

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem signedScale_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good ∅ u J a)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (sign : Bool) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let start := (signedState regs (Squarefree.ScaleProgram.idle e (Product.bytes a) []) sign).withPC
      (some signedScaleProgram.entry)
    let result := signedEntries p t M cache table minusOne sign a
    ∃ steps rr, steps ≤ signedScalingBudget n (baseWidth p t) d u J ∧
      Trace signedScaleProgram steps start
        ((signedState rr {Squarefree.ScaleProgram.idle e [] [] with
          output := Product.bytes result} sign).withPC none) ∧ Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace signedScaleProgram prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + signedScalingBudget n (baseWidth p t) d u J := by
  sorry

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
end
