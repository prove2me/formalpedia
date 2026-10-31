-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeConcrete_completedRows_origin
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:24:04.441968+00:00
-- url     : https://prove2.me/theorems/85848d40-8967-495b-b167-fb1e99fe436f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcreteTarget.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcreteTarget.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking`, `open LayoutProgram PerturbationAssembly`):
--
--   ```lean
--   theorem completedRows_origin (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (H : Finset (Fin n)) (f : ℕ) (j v : ResidualEmbedding.Free H) :
--       (completedRows p ps P H f j.val v).eval 0 = if v=j then 1 else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows` (definitions bundle `OAIQ081S181` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcreteTarget.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin)

import Mathlib
import Definitions.Def_OAIQ081S181

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

theorem completedRows_origin (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j v : ResidualEmbedding.Free H) :
    (completedRows p ps P H f j.val v).eval 0 = if v=j then 1 else 0 := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end
