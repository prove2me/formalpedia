-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Source_native_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:51:13.064152+00:00
-- url     : https://prove2.me/theorems/c34b5cf5-537f-4a6a-a7e3-008bc9e81a9c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexponentialSAT.Subexp`, `open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram`, `open LayoutSourceRowsProgram`):
--
--   ```lean
--   theorem native_command_eval {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (a : Source.Data) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
--       (h : NativeInput p ps P a v N f S width frame) :
--       ∃ (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
--         (raw : List (List (DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)))
--         (n : ℕ) (rf rr : Fin 16 → Bool),
--         rows.map Subtype.val = raw ∧ rows.length = N ∧
--         RowProperty DensePolynomialProgram.Fixed.encode
--           (fun j out => PolynomialExecutorProgram.meaning p.ops out.val =
--             sourceRowFamily ps N f v (totalPackedSource p P) j)
--           ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧
--         n ≤ nativeRowsBudget p (nativeStore a) v N f S ps ∧
--         Eval Source.command (Source.cost a (nativeResult p (nativeStore a) raw rf) n) a
--           (⟨rr,Function.update a.stacks 545
--             (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : Source.Data)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowProperty` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowFamily` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.cost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.nativeStore` (definitions bundle `OAIQ081S159` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.totalPackedSource` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.nativeResult` (definitions bundle `OAIQ081S170` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.NativeInput` (definitions bundle `OAIQ081S182` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.command` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_bound` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramSourceNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

theorem native_command_eval {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : Source.Data) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (h : NativeInput p ps P a v N f S width frame) :
    ∃ (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
      (raw : List (List (DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)))
      (n : ℕ) (rf rr : Fin 16 → Bool),
      rows.map Subtype.val = raw ∧ rows.length = N ∧
      RowProperty DensePolynomialProgram.Fixed.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out.val =
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧
      n ≤ nativeRowsBudget p (nativeStore a) v N f S ps ∧
      Eval Source.command (Source.cost a (nativeResult p (nativeStore a) raw rf) n) a
        (⟨rr,Function.update a.stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : Source.Data) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end
