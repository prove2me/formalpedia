-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_LocalValue_corrected_denote
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:38:55.16473+00:00
-- url     : https://prove2.me/theorems/4d0231a1-b9b5-405a-be8f-f1734e79bc65
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramLocalValue.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramLocalValue.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue`, with `open SubexponentialSAT Polynomial`, `open SubexpSymbolicCost DensePolynomialProgram`, `open CRTLocalProgram`):
--
--   ```lean
--   theorem corrected_denote (ops : RepresentedRing (Coeff B d) R) (minusOne : Coeff B d)
--       (hn : ops.decode minusOne = -1) (nodes : Fin Q → Coeff B d)
--       (q t J : ℕ) (jets : Fin Q → Model.Poly B d J) (i : Fin Q)
--       (c : Coeff B d) (rest : List (Coeff B d))
--       (hhead : (factorCode ops minusOne nodes J i).1 = c :: rest) :
--       Model.denote ops.decode (Model.corrected ops minusOne c q t
--         (factorCode ops minusOne nodes J i) (jets i)) =
--         TruncatedInverse.correction (fun j => ops.decode (nodes j)) J
--           (inverse (fun j => ops.decode (nodes j)) q t J)
--           (fun j => Model.denote ops.decode (jets j)) i
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.TruncatedInverse.correction` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.inverse` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.denote` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.factorCode` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramLocalValue.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote)

import Mathlib
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

open SubexponentialSAT Polynomial
open SubexpSymbolicCost DensePolynomialProgram
open CRTLocalProgram

variable {B d J Q : ℕ} {R : Type*} [CommRing R]

theorem corrected_denote (ops : RepresentedRing (Coeff B d) R) (minusOne : Coeff B d)
    (hn : ops.decode minusOne = -1) (nodes : Fin Q → Coeff B d)
    (q t J : ℕ) (jets : Fin Q → Model.Poly B d J) (i : Fin Q)
    (c : Coeff B d) (rest : List (Coeff B d))
    (hhead : (factorCode ops minusOne nodes J i).1 = c :: rest) :
    Model.denote ops.decode (Model.corrected ops minusOne c q t
      (factorCode ops minusOne nodes J i) (jets i)) =
      TruncatedInverse.correction (fun j => ops.decode (nodes j)) J
        (inverse (fun j => ops.decode (nodes j)) q t J)
        (fun j => Model.denote ops.decode (jets j)) i := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

end OAI.Algorithms
end
