-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryProducerSpace_low_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:00:47.116074+00:00
-- url     : https://prove2.me/theorems/9e8856af-8b9d-46c7-bd54-fb7091d69070
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryIncidenceSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryIncidenceSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace`, with `open OAI BitProgram StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram TruncatedRingProgram`, `open scoped BigOperators`):
--
--   ```lean
--   theorem low_run_space (t : ℕ) {d : ℕ} (model : RingModel.Data d)
--       (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
--       (J N : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
--       (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
--       (low : SubexpConvolutionControl.Store)
--       (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
--       (hout : low 217 = []) (regs : Fin 16 → Bool) :
--       let source := emittedSource t model M cache J N theta rows
--       let bound := PerturbationAssembly.lowWorkPolynomial rows.length N J t d
--         ((low 192).length + (low 193).length + (low 243).length) + 1
--       ∃ steps rr, steps ≤ bound ∧
--         Trace lowProgram steps
--           ((⟨regs, low⟩ : State 16 256).withPC (some lowProgram.entry))
--           ((⟨rr, Function.update low 217 (Product.bytes source)⟩ : State 16 256).withPC none) ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ steps →
--           Trace lowProgram prefixSteps
--             ((⟨regs, low⟩ : State 16 256).withPC (some lowProgram.entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤ stackBits low + bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.stackBits` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.lowWorkPolynomial` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.emittedSource` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.prepareLow` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.lowProgram` (definitions bundle `OAIQ081S188` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryIncidenceSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space)

import Mathlib
import Definitions.Def_OAIQ081S188

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

theorem low_run_space (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (low : SubexpConvolutionControl.Store)
    (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
    (hout : low 217 = []) (regs : Fin 16 → Bool) :
    let source := emittedSource t model M cache J N theta rows
    let bound := PerturbationAssembly.lowWorkPolynomial rows.length N J t d
      ((low 192).length + (low 193).length + (low 243).length) + 1
    ∃ steps rr, steps ≤ bound ∧
      Trace lowProgram steps
        ((⟨regs, low⟩ : State 16 256).withPC (some lowProgram.entry))
        ((⟨rr, Function.update low 217 (Product.bytes source)⟩ : State 16 256).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace lowProgram prefixSteps
          ((⟨regs, low⟩ : State 16 256).withPC (some lowProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits low + bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end
