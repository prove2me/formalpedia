-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceForOwner_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:58:41.152738+00:00
-- url     : https://prove2.me/theorems/e9cad8d2-d56a-492d-9c6e-b58569da972a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem sourceForOwner_run (source : Code) (base : Store) (encode : Witness → List Bool)
--       (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
--       (query : ℕ) (ps : List (ℕ × ℕ))
--       (hq : base 320=LayoutOwnerFiberProgram.unary query)
--       (hs : base 337=LayoutOwnerFiberProgram.stream ps)
--       (hclean : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
--       (h305 : base 305=[]) (h287 : base 287=[]) (h333 : base 333=[])
--       (hI : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ I)
--       (regs : Fin 16 → Bool) :
--       ∃ ws n rf, List.Forall₂ R (LayoutOwnerFiberProgram.fiberIndices query 0 ps) ws ∧
--         n ≤ LayoutOwnerFiberProgram.budget query ps+
--           (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(K+5*I+3*L+15)+6 ∧
--         Eval (sourceForOwner source) n (⟨regs,base⟩ : Data)
--           (⟨rf,Function.update base 333 ([false,false]++emittedBytes encode ws).reverse⟩ : Data)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.fiberIndices` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.unary` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.emittedBytes` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ownerStacks` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RelSourceSpec` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {Witness : Type*}

theorem sourceForOwner_run (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : base 320=LayoutOwnerFiberProgram.unary query)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (hclean : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (h305 : base 305=[]) (h287 : base 287=[]) (h333 : base 333=[])
    (hI : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ I)
    (regs : Fin 16 → Bool) :
    ∃ ws n rf, List.Forall₂ R (LayoutOwnerFiberProgram.fiberIndices query 0 ps) ws ∧
      n ≤ LayoutOwnerFiberProgram.budget query ps+
        (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(K+5*I+3*L+15)+6 ∧
      Eval (sourceForOwner source) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 333 ([false,false]++emittedBytes encode ws).reverse⟩ : Data) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end
