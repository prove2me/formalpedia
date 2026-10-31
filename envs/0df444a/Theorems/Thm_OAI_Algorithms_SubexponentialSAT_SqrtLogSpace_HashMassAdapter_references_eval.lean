-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMassAdapter_references_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:14:21.65562+00:00
-- url     : https://prove2.me/theorems/768e958a-9eb7-4418-b3d8-1c50e86bf8f5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashMassAdapter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashMassAdapter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter`, with `open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram`, `open LeafOuterProgram`):
--
--   ```lean
--   theorem references_eval (a : Data) (ha : ReferencesReady a) :
--       ∃ t b, t ≤ routeCost (782,0) a+LeafOuterNative.References.budget (a.stacks 782)+1 ∧
--         Eval references t a b ∧ b.stacks=Function.update a.stacks 320
--           (ProgramEncoding.encodeRecords (RowSelectionProgram.Index.alphabet
--             (CounterPrograms.value (a.stacks 782))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNative.References.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.alphabet` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.routeCost` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Data` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.ReferencesReady` (definitions bundle `OAIQ081S151` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.mass_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.mass_halt_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashMassAdapter.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval)

import Mathlib
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

variable {X Row : Type*} [Fintype X] {m : ℕ}

open LeafOuterProgram

theorem references_eval (a : Data) (ha : ReferencesReady a) :
    ∃ t b, t ≤ routeCost (782,0) a+LeafOuterNative.References.budget (a.stacks 782)+1 ∧
      Eval references t a b ∧ b.stacks=Function.update a.stacks 320
        (ProgramEncoding.encodeRecords (RowSelectionProgram.Index.alphabet
          (CounterPrograms.value (a.stacks 782)))) := by
  sorry

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end
