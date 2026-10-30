-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_scalar_value_eq_target
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:55:00.972133+00:00
-- url     : https://prove2.me/theorems/9912a08e-546a-4f17-84ce-4c7a1f1c5d9c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramResult.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramResult.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram`, with `open SubexponentialSAT Polynomial`):
--
--   ```lean
--   theorem scalar_value_eq_target {Q : ℕ} [NeZero Q]
--       (theta : Fin Q → model.O t) (J : ℕ) (hJ : 0 < J)
--       (hnodes : Function.Injective (fun i => model.rho t ht (theta i)))
--       (inverse : Fin Q → model.O t) (jets : Fin Q → (model.O t)[X])
--       (hinverse : ∀ i, inverse i * (TruncatedInverse.localFactor theta J i).coeff 0 = 1)
--       (target : (model.O t)[X]) (hdegree : target.natDegree < Q * J)
--       (hjets : ∀ i, Truncation.trunc J (jets i) = JetCRT.jet (theta i) J target) :
--       SubexpCRTAtZero.value theta J inverse jets = target.eval 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.JetCRT.jet` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Truncation.trunc` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.residuePolynomial` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.TruncatedInverse.localFactor` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.E`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.rho` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTAtZero.value` (definitions bundle `OAIQ081S081` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramResult.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target)

import Mathlib
import Definitions.Def_OAIQ081S081

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT Polynomial

variable {d : ℕ} (model : RingModel.Data d) (t : ℕ) (ht : 0 < t)

theorem scalar_value_eq_target {Q : ℕ} [NeZero Q]
    (theta : Fin Q → model.O t) (J : ℕ) (hJ : 0 < J)
    (hnodes : Function.Injective (fun i => model.rho t ht (theta i)))
    (inverse : Fin Q → model.O t) (jets : Fin Q → (model.O t)[X])
    (hinverse : ∀ i, inverse i * (TruncatedInverse.localFactor theta J i).coeff 0 = 1)
    (target : (model.O t)[X]) (hdegree : target.natDegree < Q * J)
    (hjets : ∀ i, Truncation.trunc J (jets i) = JetCRT.jet (theta i) J target) :
    SubexpCRTAtZero.value theta J inverse jets = target.eval 0 := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end

end OAI.Algorithms
end
