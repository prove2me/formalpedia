-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationBetaProgram_betaCommand_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:25:49.871155+00:00
-- url     : https://prove2.me/theorems/75065d9f-9654-4286-8248-7f1f598e77d5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationBetaProgramRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationBetaProgramRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing`, `open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)`):
--
--   ```lean
--   theorem betaCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
--       (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
--         (HornerProgram.modelTable t a M cache) base)
--       (theta : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
--       (hL : ∀ row∈rows,row.1.length=L)
--       (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
--       (h207 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
--       (h209 : base 209=RingProgram.flat theta)
--       (h210 : (base 210).length=L) (h211 : (base 211).length=d*baseWidth 3 t)
--       (he : WorkEmpty base) :
--       ExecutesIn betaCommand (runBudget base rows.length L t d) base
--         (Function.update base 220 (RingProgram.flat (runValue t a M cache theta rows)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.Store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.WorkEmpty` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.runBudget` (definitions bundle `OAIQ081S080` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.NativeReady` (definitions bundle `OAIQ081S116` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.rowsBits` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.runValue` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand` (definitions bundle `OAIQ081S184` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationBetaProgramRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.betaCommand_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S184

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

theorem betaCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
    (h207 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h209 : base 209=RingProgram.flat theta)
    (h210 : (base 210).length=L) (h211 : (base 211).length=d*baseWidth 3 t)
    (he : WorkEmpty base) :
    ExecutesIn betaCommand (runBudget base rows.length L t d) base
      (Function.update base 220 (RingProgram.flat (runValue t a M cache theta rows))) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end
