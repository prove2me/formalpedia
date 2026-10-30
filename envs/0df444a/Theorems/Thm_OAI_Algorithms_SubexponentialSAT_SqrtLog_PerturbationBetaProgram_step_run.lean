-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationBetaProgram_step_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:31:40.666979+00:00
-- url     : https://prove2.me/theorems/ea43d411-7a00-42ff-a40a-deb709c389a2
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationBetaProgramStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationBetaProgramStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing`, `open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)`):
--
--   ```lean
--   theorem step_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
--       (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
--         (HornerProgram.modelTable t a M cache) base)
--       (theta acc : Coeff t d) (P : List (Coeff t d)) (b : Bool)
--       (rows : List (List (Coeff t d) × Bool))
--       (hx : base 247=RingProgram.flat theta)
--       (hz0 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
--       (hc : (base 210).length=P.length) (hw : (base 250).length=d*baseWidth 3 t)
--       (h232 : base 232=[]) (h240 : base 240=[]) (h246 : base 246=[])
--       (h248 : base 248=[]) (h241 : base 241=[]) (h244 : base 244=[])
--       (h245 : base 245=[]) (h251 : base 251=[]) (h252 : base 252=[]) :
--       ExecutesIn step (stepBudget P.length t d) (ready base ((P,b)::rows) acc)
--         (ready base rows (stepValue t a M cache theta acc (P,b)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.Store` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.stepBudget` (definitions bundle `OAIQ081S080` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.NativeReady` (definitions bundle `OAIQ081S116` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.ready` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.stepValue` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step` (definitions bundle `OAIQ081S163` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationBetaProgramStep.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S163

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

theorem step_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta acc : Coeff t d) (P : List (Coeff t d)) (b : Bool)
    (rows : List (List (Coeff t d) × Bool))
    (hx : base 247=RingProgram.flat theta)
    (hz0 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (base 210).length=P.length) (hw : (base 250).length=d*baseWidth 3 t)
    (h232 : base 232=[]) (h240 : base 240=[]) (h246 : base 246=[])
    (h248 : base 248=[]) (h241 : base 241=[]) (h244 : base 244=[])
    (h245 : base 245=[]) (h251 : base 251=[]) (h252 : base 252=[]) :
    ExecutesIn step (stepBudget P.length t d) (ready base ((P,b)::rows) acc)
      (ready base rows (stepValue t a M cache theta acc (P,b))) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end
