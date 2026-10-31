-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_Bounds_prepareHead_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:01:17.174962+00:00
-- url     : https://prove2.me/theorems/d0ad8ef9-ea0d-4fbd-b9b4-5dd1bef3546f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramBoundsPrepare.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramBoundsPrepare.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage`):
--
--   ```lean
--    theorem prepareHead_bound (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
--       (rows : List (List Bool)) (low : List Bool) (W z A : ℕ)
--       (ha : WordBound A a) (hsize : n ≤ rows.length) :
--       let s := preparationSize n N rows low W z
--       WordBound (A+5*s^2) (preparedHead a regs n N rows low W z) ∧
--       prepareHeadCost a regs n N rows low W z ≤ 100000*(A+s^3+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.preparationSize` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHeadCost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.preparedHead` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramBoundsPrepare.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem prepareHead_bound (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z A : ℕ)
    (ha : WordBound A a) (hsize : n ≤ rows.length) :
    let s := preparationSize n N rows low W z
    WordBound (A+5*s^2) (preparedHead a regs n N rows low W z) ∧
    prepareHeadCost a regs n N rows low W z ≤ 100000*(A+s^3+1) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
end
