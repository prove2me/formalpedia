-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighBranchSpace_prepare_high_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:37:56.275715+00:00
-- url     : https://prove2.me/theorems/41c3101d-fdd1-4730-9569-b2d2ffe6b3f1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighBranchSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighBranchSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace`, with `open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram`):
--
--   ```lean
--   theorem prepare_high_space (a : Data) (words : List (List Bool)) (h localCap bound : ℕ)
--       (input output : Fin 896)
--       (hc : a.stacks 330=ProgramEncoding.encodeRecords words)
--       (hshape : words.map List.length=List.replicate h 1)
--       (hh : h=Restriction.highCount (a.stacks 338))
--       (hcounter : (a.stacks 330).length≤localCap) (hmask : (a.stacks 338).length≤localCap)
--       (hbudget : 67*localCap+37≤bound) (hb : ∀ i, (a.stacks i).length≤bound) :
--       ∃ steps regs, Trace (compiled prepareHigh input output) steps
--         (a.withPC (some (compiled prepareHigh input output).entry))
--         ((highResult (resetHighState a) regs words.flatten).withPC none) ∧
--         steps ≤ 18 * bound + 65 * (a.stacks 338).length + 68 ∧
--         ∀ (q : ℕ) z, q ≤ steps → Trace (compiled prepareHigh input output) q
--           (a.withPC (some (compiled prepareHigh input output).entry)) z →
--           ∀ i, (z.stacks i).length≤bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.highResult` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.resetHighState` (definitions bundle `OAIQ081S165` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighBranchSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space)

import Mathlib
import Definitions.Def_OAIQ081S165

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

theorem prepare_high_space (a : Data) (words : List (List Bool)) (h localCap bound : ℕ)
    (input output : Fin 896)
    (hc : a.stacks 330=ProgramEncoding.encodeRecords words)
    (hshape : words.map List.length=List.replicate h 1)
    (hh : h=Restriction.highCount (a.stacks 338))
    (hcounter : (a.stacks 330).length≤localCap) (hmask : (a.stacks 338).length≤localCap)
    (hbudget : 67*localCap+37≤bound) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ steps regs, Trace (compiled prepareHigh input output) steps
      (a.withPC (some (compiled prepareHigh input output).entry))
      ((highResult (resetHighState a) regs words.flatten).withPC none) ∧
      steps ≤ 18 * bound + 65 * (a.stacks 338).length + 68 ∧
      ∀ (q : ℕ) z, q ≤ steps → Trace (compiled prepareHigh input output) q
        (a.withPC (some (compiled prepareHigh input output).entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace
end
