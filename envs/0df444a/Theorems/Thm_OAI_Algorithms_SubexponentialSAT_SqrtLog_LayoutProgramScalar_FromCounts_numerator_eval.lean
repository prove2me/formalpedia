-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_FromCounts_numerator_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:30:30.075406+00:00
-- url     : https://prove2.me/theorems/902727da-f916-40f2-a054-70005ac58e77
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarFromCounts.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarFromCounts.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram`, `open LayoutTriplePreparationProgram`):
--
--   ```lean
--   theorem numerator_eval (c : Saved) (cache : Cache) (regs : Fin 9 → Bool)
--       (n ac : List Bool) (A R d h Q : ℕ)
--       (hp : cache.Hpositive.flatten=c.hp) (hn : cache.Hnegative.flatten=c.hn)
--       (hw : cache.width=c.width) (hpower : cache.power=c.power)
--       (hc : n.length=R-d) (ha : ac.length=A)
--       (hu : cache.Uniform) (hf : cache.Fits (R-d)) (hv : cache.Values A R h) (hm : cache.Totals A R h)
--       (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (hhQ : h ≤ Q) :
--       ∃ t ≤ numeratorPrepareCost (R-d) A c.width.length (pairLength c.power)+
--         numeratorFoldCost (R-d) c.width.length (pairLength c.power)+1,
--       ∃ rf result, Eval numerator t
--         (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[]))
--         (state c rf [] [] [] [] [] cache.Bpositive.flatten cache.Bnegative.flatten result) ∧
--         pairValue result=LayoutCoefficientAlgorithm.scalarSum A R d h ∧
--         wordTotal result ≤ (8*Q)^(2*R) ∧
--         pairLength result ≤ (R-d)*termGrowth (2*c.width.length+pairLength c.power)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarSum` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termGrowth` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.numeratorPrepareCost` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.numeratorFoldCost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.Saved` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Fits` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Uniform` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Totals` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Values` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator` (definitions bundle `OAIQ081S123` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.state` (definitions bundle `OAIQ081S125` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarFromCounts.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval)

import Mathlib
import Definitions.Def_OAIQ081S123
import Definitions.Def_OAIQ081S125

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

theorem numerator_eval (c : Saved) (cache : Cache) (regs : Fin 9 → Bool)
    (n ac : List Bool) (A R d h Q : ℕ)
    (hp : cache.Hpositive.flatten=c.hp) (hn : cache.Hnegative.flatten=c.hn)
    (hw : cache.width=c.width) (hpower : cache.power=c.power)
    (hc : n.length=R-d) (ha : ac.length=A)
    (hu : cache.Uniform) (hf : cache.Fits (R-d)) (hv : cache.Values A R h) (hm : cache.Totals A R h)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (hhQ : h ≤ Q) :
    ∃ t ≤ numeratorPrepareCost (R-d) A c.width.length (pairLength c.power)+
      numeratorFoldCost (R-d) c.width.length (pairLength c.power)+1,
    ∃ rf result, Eval numerator t
      (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[]))
      (state c rf [] [] [] [] [] cache.Bpositive.flatten cache.Bnegative.flatten result) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum A R d h ∧
      wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*termGrowth (2*c.width.length+pairLength c.power) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end
