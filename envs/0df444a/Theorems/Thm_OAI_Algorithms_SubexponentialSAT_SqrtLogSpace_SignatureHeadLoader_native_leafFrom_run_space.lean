-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_native_leafFrom_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:18:44.492147+00:00
-- url     : https://prove2.me/theorems/7a7f55c3-2cd8-448a-bd4b-e22c37e8a51f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoader.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoader.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram`, `open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`):
--
--   ```lean
--   theorem native_leafFrom_run_space (src : Fin 896) (s : Native.Inputs)
--       (a : Data) (ha : Native.Ready s a) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
--       (words : List (List Bool)) (hw : CacheCorrect s.height (unary s.R) s.width words)
--       (frame : State 40 896)
--       (hf : MasterFrame (Native.start s a ra rd rc words) (projectState leafRegs lowStacks frame))
--       (z A : ℕ) (hs : src∉([649,659,846,847] : List (Fin 896)))
--       (hz : frame.stacks src=unary z)
--       (hA : WordBound A frame) :
--       ∃ rp rm rs raw shifted total,
--         total ≤ 36*A+22*(localWork s z A+1)+35 ∧
--         Trace (programFrom src) total (frame.withPC (some (programFrom src).entry))
--           ((leafOutputFrom src frame (localResult (leafInputFrom src frame) rp rm rs
--             s.n s.N (s.Q*s.r) z s.rows s.low raw shifted)).withPC none) ∧
--         LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
--           (selectedHeads s.n s.rows s.low z) raw ∧
--         List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
--         ∀ prefixSteps intermediate,prefixSteps ≤ total →
--           Trace (programFrom src) prefixSteps (frame.withPC (some (programFrom src).entry)) intermediate →
--           dataBits intermediate ≤ 1000*(A+(localWork s z A+1)+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.SignedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.dataBits` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.relation` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafInputFrom`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafOutputFrom` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localWork` (definitions bundle `OAIQ081S179` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.programFrom` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.programFromLabels` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.load_run_polynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoader.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space)

import Mathlib
import Definitions.Def_OAIQ081S191

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem native_leafFrom_run_space (src : Fin 896) (s : Native.Inputs)
    (a : Data) (ha : Native.Ready s a) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (words : List (List Bool)) (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hf : MasterFrame (Native.start s a ra rd rc words) (projectState leafRegs lowStacks frame))
    (z A : ℕ) (hs : src∉([649,659,846,847] : List (Fin 896)))
    (hz : frame.stacks src=unary z)
    (hA : WordBound A frame) :
    ∃ rp rm rs raw shifted total,
      total ≤ 36*A+22*(localWork s z A+1)+35 ∧
      Trace (programFrom src) total (frame.withPC (some (programFrom src).entry))
        ((leafOutputFrom src frame (localResult (leafInputFrom src frame) rp rm rs
          s.n s.N (s.Q*s.r) z s.rows s.low raw shifted)).withPC none) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace (programFrom src) prefixSteps (frame.withPC (some (programFrom src).entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+(localWork s z A+1)+1) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end
