-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_raw_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:00:51.201376+00:00
-- url     : https://prove2.me/theorems/d981836a-93b3-4a28-a836-cdfce62ac7ea
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram`, `open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`):
--
--   ```lean
--   theorem raw_eval (a : Data) (D n : ℕ) (js : List ℕ)
--       (hD : a.stacks 647=List.replicate D true)
--       (hi : a.stacks 650=LayoutMatrixProgram.ids js)
--       (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
--       (T B : ℕ)
--       (hc : LayoutMatrixProgram.EntryContract entry (matrixBase a) Valid Rel T B)
--       (hv : ∀ j<D,∀ v∈js,Valid j v) (hjs : ∀ v∈js,v ≤ n) :
--       ∃ rf rows t,
--         LayoutMatrixProgram.MatrixRel Rel B D js rows ∧
--         t ≤ stageCost id (by decide) matrixInputs rawOutputs a
--           (LayoutMatrixProgram.finalState (matrixBase a) rf rows)
--           (LayoutMatrixProgram.commandCost T B D n js+1) ∧
--         Eval rawCommand t a (returned id (by decide) matrixInputs rawOutputs a
--           (LayoutMatrixProgram.finalState (matrixBase a) rf rows)) ∧
--         (returned id (by decide) matrixInputs rawOutputs a
--           (LayoutMatrixProgram.finalState (matrixBase a) rf rows)).stacks 669=
--             LayoutMatrixProgram.rowsWords rows ∧
--         ∀ A,WordBound A a →
--           t ≤ (LayoutMatrixProgram.commandCost T B D n js+1)+
--             1878*(A+(LayoutMatrixProgram.commandCost T B D n js+1)+1) ∧
--           WordBound (A+(LayoutMatrixProgram.commandCost T B D n js+1))
--             (returned id (by decide) matrixInputs rawOutputs a
--               (LayoutMatrixProgram.finalState (matrixBase a) rf rows))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Pair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.matrixInputs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.rawOutputs` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.commandCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.ids` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowsWords` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.returned` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stageCost` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.EntryContract` (definitions bundle `OAIQ081S122` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.finalState` (definitions bundle `OAIQ081S123` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.matrixBase` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.entry` (definitions bundle `OAIQ081S184` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.rawCommand` (definitions bundle `OAIQ081S187` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval)

import Mathlib
import Definitions.Def_OAIQ081S187

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem raw_eval (a : Data) (D n : ℕ) (js : List ℕ)
    (hD : a.stacks 647=List.replicate D true)
    (hi : a.stacks 650=LayoutMatrixProgram.ids js)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (T B : ℕ)
    (hc : LayoutMatrixProgram.EntryContract entry (matrixBase a) Valid Rel T B)
    (hv : ∀ j<D,∀ v∈js,Valid j v) (hjs : ∀ v∈js,v ≤ n) :
    ∃ rf rows t,
      LayoutMatrixProgram.MatrixRel Rel B D js rows ∧
      t ≤ stageCost id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)
        (LayoutMatrixProgram.commandCost T B D n js+1) ∧
      Eval rawCommand t a (returned id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)) ∧
      (returned id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)).stacks 669=
          LayoutMatrixProgram.rowsWords rows ∧
      ∀ A,WordBound A a →
        t ≤ (LayoutMatrixProgram.commandCost T B D n js+1)+
          1878*(A+(LayoutMatrixProgram.commandCost T B D n js+1)+1) ∧
        WordBound (A+(LayoutMatrixProgram.commandCost T B D n js+1))
          (returned id (by decide) matrixInputs rawOutputs a
            (LayoutMatrixProgram.finalState (matrixBase a) rf rows)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end
