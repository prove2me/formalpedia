-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_SparseCode_supplied_kernel_bound_of_coverage
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:49:29.524128+00:00
-- url     : https://prove2.me/theorems/e7f4d476-0383-4749-a369-b2f811a08cee
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SparseCodeSupplied.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SparseCodeSupplied.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem supplied_kernel_bound_of_coverage {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
--       (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
--       (hs : WalshExistence.Good (gapDenom m B) s)
--       (hQ : HasDistance Q (degree m B / (100 * B * logSize m) + 1))
--       (rs : List (Fin m → F3))
--       (hcover : ∀ i, suppliedMatrix m B hm hB s Q i ∈ rs)
--       (w : Fin m → F3) (hw : ∀ r ∈ rs, (∑ c, r c*w c)=0) (hw0 : w≠0) :
--       m ≤ distanceDenom m B*weight w
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.gapDenom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.weight` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.totalRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.suppliedMatrix` (definitions bundle `OAIQ081S063` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SparseCodeSupplied.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage)

import Mathlib
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S063

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

theorem supplied_kernel_bound_of_coverage {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100 * B * logSize m) + 1))
    (rs : List (Fin m → F3))
    (hcover : ∀ i, suppliedMatrix m B hm hB s Q i ∈ rs)
    (w : Fin m → F3) (hw : ∀ r ∈ rs, (∑ c, r c*w c)=0) (hw0 : w≠0) :
    m ≤ distanceDenom m B*weight w := by
  sorry

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end
