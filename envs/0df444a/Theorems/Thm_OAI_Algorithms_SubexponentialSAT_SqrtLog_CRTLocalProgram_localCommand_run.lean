-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_localCommand_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:23:10.912975+00:00
-- url     : https://prove2.me/theorems/0ff810c9-a9c8-4802-b948-a24147cb2e1b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramExecutionComplete.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramExecutionComplete.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl`):
--
--   ```lean
--   theorem localCommand_run {C P : Type*} (s : Store)
--       (encC : C → List Bool) (encP : P → List Bool)
--       (constant linear : C → P) (sm sa pm pa : Code)
--       (cm ca : C → C → C) (mulP addP : P → P → P)
--       (Km Ka Kp Kap W V J : ℕ) (hW : 0 < W)
--       (hsm : ServiceSpec s encC sm cm Km) (hsa : ServiceSpec s encC sa ca Ka)
--       (hpm : ServiceSpec s encP pm mulP Kp) (hpa : ServiceSpec s encP pa addP Kap)
--       (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
--       (zero one minusOne theta c : C) (cs : List C) (jet : P) (rest : List Bool)
--       (hconstant : ∀ a, encP (constant a) =
--         DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
--       (hlinear : ∀ a, encP (linear a) =
--         DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC one) J)
--       (hzero : s 104 = encC zero) (hzeroBits : encC zero = List.replicate W false)
--       (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
--       (htheta : s 213 = encC theta) (hcs : s 214 = cs.flatMap encC)
--       (hJ : s 243 = List.replicate J true) (hjet : s 225 = encP jet)
--       (hpolyZero : s 192 = encP (constant zero))
--       (hclean : ∀ i ∈ localWork, s i = [])
--       (hhead : 0 < J → encP ((cs.eraseIdx (s 216).length).foldl
--         (localUpdate cm ca mulP linear theta minusOne J) (constant one)) = encC c ++ rest) :
--       let factor := (cs.eraseIdx (s 216).length).foldl
--         (localUpdate cm ca mulP linear theta minusOne J) (constant one)
--       let inv := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
--       let out := if J = 0 then [] else encP (correctionValue mulP addP (constant zero) (constant one)
--           (constant (cm inv minusOne)) (constant inv) factor jet J)
--       ExecutesIn (localCommand sm sa pm pa)
--         (localBudget cs.length (s 216).length (s 209).length (s 212).length J Km Ka Kp Kap W V)
--         s (Function.update s 244 out)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Store` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseValue` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localBudget` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localWork` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor.Counter.paddedBits` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localUpdate` (definitions bundle `OAIQ081S028` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand` (definitions bundle `OAIQ081S116` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramExecutionComplete.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run)

import Mathlib
import Definitions.Def_OAIQ081S116

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem localCommand_run {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool)
    (constant linear : C → P) (sm sa pm pa : Code)
    (cm ca : C → C → C) (mulP addP : P → P → P)
    (Km Ka Kp Kap W V J : ℕ) (hW : 0 < W)
    (hsm : ServiceSpec s encC sm cm Km) (hsa : ServiceSpec s encC sa ca Ka)
    (hpm : ServiceSpec s encP pm mulP Kp) (hpa : ServiceSpec s encP pa addP Kap)
    (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
    (zero one minusOne theta c : C) (cs : List C) (jet : P) (rest : List Bool)
    (hconstant : ∀ a, encP (constant a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
    (hlinear : ∀ a, encP (linear a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC one) J)
    (hzero : s 104 = encC zero) (hzeroBits : encC zero = List.replicate W false)
    (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
    (htheta : s 213 = encC theta) (hcs : s 214 = cs.flatMap encC)
    (hJ : s 243 = List.replicate J true) (hjet : s 225 = encP jet)
    (hpolyZero : s 192 = encP (constant zero))
    (hclean : ∀ i ∈ localWork, s i = [])
    (hhead : 0 < J → encP ((cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)) = encC c ++ rest) :
    let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)
    let inv := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    let out := if J = 0 then [] else encP (correctionValue mulP addP (constant zero) (constant one)
        (constant (cm inv minusOne)) (constant inv) factor jet J)
    ExecutesIn (localCommand sm sa pm pa)
      (localBudget cs.length (s 216).length (s 209).length (s 212).length J Km Ka Kp Kap W V)
      s (Function.update s 244 out) := by
  sorry

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end
