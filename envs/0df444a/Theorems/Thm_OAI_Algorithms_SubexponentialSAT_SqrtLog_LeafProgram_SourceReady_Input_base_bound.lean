-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_SourceReady_Input_base_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:50:33.452053+00:00
-- url     : https://prove2.me/theorems/a6e4b893-d1cb-4a76-a296-3b28a8ca36ac
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceReadySize.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceReadySize.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram`, `open LayoutSourceRowsProgram`):
--
--   ```lean
--   theorem Input.base_bound (h : Input p ps P a v N f S) (i : Fin 340) :
--       (sourceBase a (p.R+1) (d*baseWidth 3 p.t) ps v N f i).length ≤ S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Data` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.sourceBase` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input` (definitions bundle `OAIQ081S170` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.native` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceReadySize.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound)

import Mathlib
import Definitions.Def_OAIQ081S170

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.base_bound (h : Input p ps P a v N f S) (i : Fin 340) :
    (sourceBase a (p.R+1) (d*baseWidth 3 p.t) ps v N f i).length ≤ S := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end
