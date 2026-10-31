-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_nativeRowsBudget_le_polynomial
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:44:46.953988+00:00
-- url     : https://prove2.me/theorems/a03b2058-cf05-4f6b-b609-3ead762c16ca
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramNativeCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramNativeCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram`, with `open SubexponentialSAT LayoutProgram`, `open SubexponentialSAT.SubexpLiftRing`):
--
--   ```lean
--   theorem nativeRowsBudget_le_polynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
--       (s : Store) (v N f S : ℕ) (ps : List (ℕ × ℕ))
--       (hv : v ≤ S) (hN : N ≤ S) (hf : f ≤ S) (hps : ps.length ≤ S)
--       (hs : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
--       (h21 : (s 21).length ≤ S) (h26 : (s 26).length ≤ S) :
--       nativeRowsBudget p s v N f S ps ≤ nativeRowsPolynomial p S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsPolynomial` (definitions bundle `OAIQ081S168` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_bound` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramNativeCost.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial)

import Mathlib
import Definitions.Def_OAIQ081S168

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT LayoutProgram
open SubexponentialSAT.SubexpLiftRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem nativeRowsBudget_le_polynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (s : Store) (v N f S : ℕ) (ps : List (ℕ × ℕ))
    (hv : v ≤ S) (hN : N ≤ S) (hf : f ≤ S) (hps : ps.length ≤ S)
    (hs : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h21 : (s 21).length ≤ S) (h26 : (s 26).length ≤ S) :
    nativeRowsBudget p s v N f S ps ≤ nativeRowsPolynomial p S := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end
