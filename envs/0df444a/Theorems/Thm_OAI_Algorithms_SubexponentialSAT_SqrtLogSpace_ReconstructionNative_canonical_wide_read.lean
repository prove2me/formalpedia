-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_ReconstructionNative_canonical_wide_read
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:49:01.47903+00:00
-- url     : https://prove2.me/theorems/4fdb6e19-5dcb-42b7-b921-e9c496d02165
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open DensePolynomialProgram`, `open LeafProgram.Count`):
--
--   ```lean
--   theorem canonical_wide_read (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
--       (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t)
--       (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
--       (hcount : count < 3^t)
--       (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (count : model.O t))
--       (a : Data) (hvalue : a.stacks 261 = RingProgram.flat x)
--       (hm : BinaryArithmetic.toNat (a.stacks 194) = 3^t)
--       (hw : (a.stacks 202).length = baseWidth 3 t)
--       (hempty : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), a.stacks i = [])
--       (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : (a.stacks 194).length ≤ S)
--       (hinput : (RingProgram.flat x).length ≤ S) :
--       ∃ (steps : ℕ) (regs : Fin 8 → Bool), steps ≤ 4400*(S+1)^2 ∧
--         Eval canonicalWideRead steps a
--           (LeafProgram.QueryReadback.Wide.completed a regs (DisjointReuse.binaryNat count))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.binaryNat` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide.completed` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonicalWideRead` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.run_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram
open LeafProgram.Count

theorem canonical_wide_read (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (count : model.O t))
    (a : Data) (hvalue : a.stacks 261 = RingProgram.flat x)
    (hm : BinaryArithmetic.toNat (a.stacks 194) = 3^t)
    (hw : (a.stacks 202).length = baseWidth 3 t)
    (hempty : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), a.stacks i = [])
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : (a.stacks 194).length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ (steps : ℕ) (regs : Fin 8 → Bool), steps ≤ 4400*(S+1)^2 ∧
      Eval canonicalWideRead steps a
        (LeafProgram.QueryReadback.Wide.completed a regs (DisjointReuse.binaryNat count)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
end
