-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_present_from_rows
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:00:02.990275+00:00
-- url     : https://prove2.me/theorems/afd40230-c091-4525-9e44-a18dfeecb11b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramAssembly.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramAssembly.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem sourceRows_present_from_rows {Witness : Type*}
--       (source : Code) (s : Store) (D W v N f : ℕ) (ps : List (ℕ × ℕ))
--       (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D W)
--       (hv : s 233=LayoutSourcePlanLookup.unary v)
--       (hN : s 212=LayoutSourcePlanLookup.unary N)
--       (hf : s 216=LayoutSourcePlanLookup.unary f)
--       (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
--       (hmem : (v,N+f) ∈ ps)
--       (hlookup : LayoutSourcePlanLookup.Native.Clean
--         (⟨fun _ => false,initializeFinish s D W⟩ : Data))
--       (encode : Witness → List Bool) (R : ℕ → Witness → Prop) (K rowWidth : ℕ)
--       (hspec : RelRowSpec (sourceRowWith source) (preparedSourceStore s D W ps v N f) encode R N K rowWidth)
--       (hclean : RowsClean (preparedSourceStore s D W ps v N f))
--       (regs : Fin 16 → Bool) :
--       ∃ ws n rf, RowProperty encode R rowWidth 0 ws ∧ ws.length=N ∧
--         n ≤ LayoutSourceRowsProgramInitialize.budget D W+
--           LayoutSourcePlanLookup.pairBudget v N f ps+N*(K+19*rowWidth+39)+
--           2*(ps.idxOf (v,N+f))+23 ∧
--         Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
--           (⟨rf,Function.update (initializeFinish s D W) 205 (Encoding.encodeList encode ws)⟩ : Data)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowProperty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowsClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializationPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializeFinish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.preparedSourceStore` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.budget` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.Ready` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.pairBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.Clean` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RelRowSpec` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowsWith` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramAssembly.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem sourceRows_present_from_rows {Witness : Type*}
    (source : Code) (s : Store) (D W v N f : ℕ) (ps : List (ℕ × ℕ))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D W)
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∈ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s D W⟩ : Data))
    (encode : Witness → List Bool) (R : ℕ → Witness → Prop) (K rowWidth : ℕ)
    (hspec : RelRowSpec (sourceRowWith source) (preparedSourceStore s D W ps v N f) encode R N K rowWidth)
    (hclean : RowsClean (preparedSourceStore s D W ps v N f))
    (regs : Fin 16 → Bool) :
    ∃ ws n rf, RowProperty encode R rowWidth 0 ws ∧ ws.length=N ∧
      n ≤ LayoutSourceRowsProgramInitialize.budget D W+
        LayoutSourcePlanLookup.pairBudget v N f ps+N*(K+19*rowWidth+39)+
        2*(ps.idxOf (v,N+f))+23 ∧
      Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s D W) 205 (Encoding.encodeList encode ws)⟩ : Data) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end
