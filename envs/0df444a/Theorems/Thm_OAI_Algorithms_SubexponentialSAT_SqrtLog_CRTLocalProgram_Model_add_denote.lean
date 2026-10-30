-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_Model_add_denote
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:05:16.313982+00:00
-- url     : https://prove2.me/theorems/20a7342d-808d-49c2-8742-8aa161b960a6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model`, with `open Polynomial`, `open SubexponentialSAT.SubexpSymbolicCost`, `open DensePolynomialProgram`):
--
--   ```lean
--   theorem add_denote {B d J : ℕ} {R : Type*} [CommRing R]
--       (ops : RepresentedRing (Coeff B d) R) (P Q : Poly B d J) :
--       denote ops.decode (Fixed.add ops.program P Q) = denote ops.decode P + denote ops.decode Q
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing.program` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.denote` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add` (definitions bundle `OAIQ081S100` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shifted_tail_polynomial` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramModel.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote)

import Mathlib
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

theorem add_denote {B d J : ℕ} {R : Type*} [CommRing R]
    (ops : RepresentedRing (Coeff B d) R) (P Q : Poly B d J) :
    denote ops.decode (Fixed.add ops.program P Q) = denote ops.decode P + denote ops.decode Q := by
  sorry

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end
