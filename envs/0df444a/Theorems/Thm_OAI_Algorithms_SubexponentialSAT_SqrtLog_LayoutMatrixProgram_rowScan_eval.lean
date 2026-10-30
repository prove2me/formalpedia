-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutMatrixProgram_rowScan_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:57:59.695295+00:00
-- url     : https://prove2.me/theorems/e99ccc39-f7e9-4d00-bc24-a7a7379bcd4c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutMatrixProgramRowScan.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutMatrixProgramRowScan.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem rowScan_eval (entry : Code 256) (base : Fin 288 → List Bool) (hb : base 286=[])
--       (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
--       (hc : EntryContract entry base Valid Rel T B) (j : ℕ) (js : List ℕ)
--       (hvalid : ∀ v ∈ js, Valid j v) (regs : Fin 16 → Bool) (q : Store)
--       (hj : q.rowIndex=List.replicate j true) (hcol : q.columnIndex=[])
--       (hp : q.positive=[]) (hn : q.negative=[]) (htodo : q.todo=ids js) :
--       ∃ t ≤ rowScanCost T B js, ∃ rf ps,
--         Eval (rowScan entry) t (state base regs q)
--           (state base rf {q with columnIndex:=[],positive:=[],negative:=[],todo:=[], row:=pairWords ps.reverse++q.row}) ∧
--         List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js ps
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScanCost` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.pairWords` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.pairLength` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.ids` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.EntryContract` (definitions bundle `OAIQ081S122` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.state` (definitions bundle `OAIQ081S123` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan` (definitions bundle `OAIQ081S143` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowLoop_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutMatrixProgramRowScan.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval)

import Mathlib
import Definitions.Def_OAIQ081S143

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rowScan_eval (entry : Code 256) (base : Fin 288 → List Bool) (hb : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (j : ℕ) (js : List ℕ)
    (hvalid : ∀ v ∈ js, Valid j v) (regs : Fin 16 → Bool) (q : Store)
    (hj : q.rowIndex=List.replicate j true) (hcol : q.columnIndex=[])
    (hp : q.positive=[]) (hn : q.negative=[]) (htodo : q.todo=ids js) :
    ∃ t ≤ rowScanCost T B js, ∃ rf ps,
      Eval (rowScan entry) t (state base regs q)
        (state base rf {q with columnIndex:=[],positive:=[],negative:=[],todo:=[], row:=pairWords ps.reverse++q.row}) ∧
      List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js ps := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end
