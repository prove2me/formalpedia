-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramReadiness_model_ready_of_low_agreement
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:00:45.899409+00:00
-- url     : https://prove2.me/theorems/45ae3df3-cd14-4089-9a05-69d92f4cc8b4
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramReadinessModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramReadinessModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness`, with `open SubexponentialSAT BitProgram StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open LayoutSourceRowsProgram`):
--
--   ```lean
--   theorem model_ready_of_low_agreement (t : ℕ) {d : ℕ} (a : RingModel.Data d)
--       (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (s after : LayoutSourceRowsProgram.Store) (D : ℕ)
--       (width : List Bool) (frame : Fin 6 → List Bool)
--       (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
--         (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
--       (E : Empty s)
--       (hf : ∀ i : Fin 340, i.val < 256 → after i = initializeFinish s D (d*baseWidth 3 t) i) :
--       PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
--         (HornerProgram.modelTable t a M cache) D width frame
--         (executionContext (evaluationInput after))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluationInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.executorPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializeFinish` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.Empty` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.executionContext` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Ready` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramReadinessModel.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutSourceRowsProgram

theorem model_ready_of_low_agreement (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s after : LayoutSourceRowsProgram.Store) (D : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
      (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
    (E : Empty s)
    (hf : ∀ i : Fin 340, i.val < 256 → after i = initializeFinish s D (d*baseWidth 3 t) i) :
    PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
      (executionContext (evaluationInput after)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness

end OAI.Algorithms
end
