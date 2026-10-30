-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_reconstructionBudget_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:42:55.343752+00:00
-- url     : https://prove2.me/theorems/f975629f-ff6e-4436-802a-1c8f9ae46392
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram`, with `open SubexponentialSAT SubexpCRTOuterProgram`):
--
--   ```lean
--   theorem reconstructionBudget_le (Q J W Km Ka Kl S : ℕ)
--       (hQ : Q ≤ S) (hJ : J ≤ S) (hW : W ≤ S)
--       (hm : Km ≤ S) (ha : Ka ≤ S) (hl : Kl ≤ S) :
--       controllerBudget W J Q (Middle.budget Q J W Km Ka Kl) + 1 ≤
--         2300 * (S + 1)^4 + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controllerBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.budget` (definitions bundle `OAIQ081S042` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.reconstructionBudget_le)

import Mathlib
import Definitions.Def_OAIQ081S042

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT SubexpCRTOuterProgram

theorem reconstructionBudget_le (Q J W Km Ka Kl S : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (hW : W ≤ S)
    (hm : Km ≤ S) (ha : Ka ≤ S) (hl : Kl ≤ S) :
    controllerBudget W J Q (Middle.budget Q J W Km Ka Kl) + 1 ≤
      2300 * (S + 1)^4 + 1 := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end
