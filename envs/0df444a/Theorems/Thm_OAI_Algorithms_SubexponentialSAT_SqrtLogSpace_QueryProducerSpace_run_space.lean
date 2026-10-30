-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryProducerSpace_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:40:41.581523+00:00
-- url     : https://prove2.me/theorems/e40afdc6-4c60-440d-9f58-9757f16c0494
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryProducerSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryProducerSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace`, with `open OAI BitProgram StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram TruncatedRingProgram`, `open scoped BigOperators`):
--
--   ```lean
--   theorem run_space (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {n d u J N : ℕ} (U : Finset (Fin n))
--       (source : List (Product.Entry n (baseWidth p t) d))
--       (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1)
--       (hN : source.length ≤ N) (regs : Fin 8 → Bool) (width degree : List Bool)
--       (hd : degree.length = d) (hw : width.length = baseWidth p t) :
--       let result := Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []
--       let start := state regs M.bits width degree [] []
--         {input := Encoding.frame (Squarefree.encodeMask U) ++ Product.bytes source}
--       ∃ steps rr, steps ≤ budget n (baseWidth p t) d u J N (Product.bytes source).length ∧
--         Trace program steps (start.withPC (some program.entry))
--           ((state rr M.bits width degree (Product.bytes result) []
--             {target := (Squarefree.encodeMask U).reverse}).withPC none) ∧
--         Good ∅ u J result ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ steps →
--           Trace program prefixSteps (start.withPC (some program.entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤ stackBits start.stacks +
--             budget n (baseWidth p t) d u J N (Product.bytes source).length
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.stackBits` and `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeMask` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.Tape` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.budget` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.ValidKey` (definitions bundle `OAIQ081S052` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation.specializeEntries` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.program` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.state` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryProducerSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

theorem run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J N : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n (baseWidth p t) d))
    (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1)
    (hN : source.length ≤ N) (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let result := Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []
    let start := state regs M.bits width degree [] []
      {input := Encoding.frame (Squarefree.encodeMask U) ++ Product.bytes source}
    ∃ steps rr, steps ≤ budget n (baseWidth p t) d u J N (Product.bytes source).length ∧
      Trace program steps (start.withPC (some program.entry))
        ((state rr M.bits width degree (Product.bytes result) []
          {target := (Squarefree.encodeMask U).reverse}).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (start.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits start.stacks +
          budget n (baseWidth p t) d u J N (Product.bytes source).length := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end
