-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpRowPostfixServices_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:56:59.990263+00:00
-- url     : https://prove2.me/theorems/ad24dc69-eb27-4df7-8606-6cf0aba0ea61
-- title:
--   OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SubexpRowPostfixServices.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpRowPostfixServices.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices`, with `open BitProgram StructuredCalls SubexpScanPrimitives`, `open SubexpConvolutionControl (Code Store Data ExecutesIn copy clear )`, `open SubexpDenseLiteralPadding (take write reset )`):
--
--   ```lean
--   theorem program_runsIn (arithmetic : Code) (K : ℕ) (s : Store)
--       (regs : Fin 16 → Bool) (left right tail out : List Bool)
--       (hin : s 27 = true :: (Encoding.frame right ++
--         (true :: (Encoding.frame left ++ tail))))
--       (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = [])
--       (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = [])
--       (harithmetic : ExecutesIn arithmetic K (prepared s left right tail)
--         (Function.update (prepared s left right tail) 244 out)) :
--       RunsIn (program arithmetic)
--         (K + 20 * (left.length + right.length) + 8 * out.length + 69)
--         ((⟨regs, s⟩ : Data).withPC (some (program arithmetic).entry))
--         ((⟨fun _ => false,
--           Function.update s 27 (true :: (Encoding.frame out ++ tail))⟩ : Data).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.prepared` (definitions bundle `OAIQ081S065` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.command` and `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.add_implements` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mul_implements` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpRowPostfixServices.lean (declaration OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S049
import Definitions.Def_OAIQ081S065
import Definitions.Def_OAIQ081S075

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpRowPostfixServices

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl (Code Store Data ExecutesIn copy clear )
open SubexpDenseLiteralPadding (take write reset )

theorem program_runsIn (arithmetic : Code) (K : ℕ) (s : Store)
    (regs : Fin 16 → Bool) (left right tail out : List Bool)
    (hin : s 27 = true :: (Encoding.frame right ++
      (true :: (Encoding.frame left ++ tail))))
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = [])
    (harithmetic : ExecutesIn arithmetic K (prepared s left right tail)
      (Function.update (prepared s left right tail) 244 out)) :
    RunsIn (program arithmetic)
      (K + 20 * (left.length + right.length) + 8 * out.length + 69)
      ((⟨regs, s⟩ : Data).withPC (some (program arithmetic).entry))
      ((⟨fun _ => false,
        Function.update s 27 (true :: (Encoding.frame out ++ tail))⟩ : Data).withPC none) := by
  sorry

end SubexponentialSAT.SubexpRowPostfixServices

end OAI.Algorithms
end
