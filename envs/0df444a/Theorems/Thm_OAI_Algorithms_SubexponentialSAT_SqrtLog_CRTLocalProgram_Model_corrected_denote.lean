-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_Model_corrected_denote
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:05:44.002784+00:00
-- url     : https://prove2.me/theorems/7f27bd5b-242b-40c7-88f1-7bfeb30bb3a6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramModelCorrectness.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramModelCorrectness.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model`, with `open Polynomial`, `open SubexponentialSAT.SubexpSymbolicCost`, `open DensePolynomialProgram`):
--
--   ```lean
--   theorem corrected_denote (ops : RepresentedRing (Coeff B d) R)
--       (minusOne c : Coeff B d) (q t : ℕ) (factor jet : Poly B d J)
--       (P : R[X]) (hn : ops.decode minusOne = -1)
--       (hfactor : denote ops.decode factor = Truncation.trunc J P) :
--       denote ops.decode (corrected ops minusOne c q t factor jet) =
--         TruncatedInverse.correctedJet P (denote ops.decode jet)
--           (ops.decode (inverseCoefficient ops minusOne c q t)) J
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.Truncation.trunc` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.TruncatedInverse.correctedJet` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.denote` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.inverseCoefficient` (definitions bundle `OAIQ081S100` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramModelCorrectness.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote)

import Mathlib
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S100

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Model
open Polynomial
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram

variable {B d J : ℕ} {R : Type*} [CommRing R]

theorem corrected_denote (ops : RepresentedRing (Coeff B d) R)
    (minusOne c : Coeff B d) (q t : ℕ) (factor jet : Poly B d J)
    (P : R[X]) (hn : ops.decode minusOne = -1)
    (hfactor : denote ops.decode factor = Truncation.trunc J P) :
    denote ops.decode (corrected ops minusOne c q t factor jet) =
      TruncatedInverse.correctedJet P (denote ops.decode jet)
        (ops.decode (inverseCoefficient ops minusOne c q t)) J := by
  sorry

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end
