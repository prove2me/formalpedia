-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_serializedRows_kernel_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:45:42.40569+00:00
-- url     : https://prove2.me/theorems/ed3fd4e4-3a47-4634-be66-368ba3aa5b97
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramSupplied.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramSupplied.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram`, with `open scoped BigOperators`, `open SparseCode`):
--
--   ```lean
--   theorem serializedRows_kernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
--       (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
--       (hs : WalshExistence.Good (gapDenom m B) s)
--       (hQ : HasDistance Q (degree m B / (100*B*logSize m)+1))
--       (w : Fin m → F3)
--       (hw : ∀ row ∈ serializedRows m s Q, (∑ c, coefficient row c*w c)=0)
--       (hw0 : w≠0) : m ≤ distanceDenom m B*weight w
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.gapDenom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.weight` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.coefficient` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.history_count` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramSupplied.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound)

import Mathlib
import Definitions.Def_OAIQ081S042
import Definitions.Def_OAIQ081S060

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SparseCode

theorem serializedRows_kernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100*B*logSize m)+1))
    (w : Fin m → F3)
    (hw : ∀ row ∈ serializedRows m s Q, (∑ c, coefficient row c*w c)=0)
    (hw0 : w≠0) : m ≤ distanceDenom m B*weight w := by
  sorry

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end
