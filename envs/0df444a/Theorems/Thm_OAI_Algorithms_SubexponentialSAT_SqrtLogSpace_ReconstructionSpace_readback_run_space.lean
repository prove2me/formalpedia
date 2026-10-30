-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_ReconstructionSpace_readback_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:21:50.259882+00:00
-- url     : https://prove2.me/theorems/9e762082-df88-46ce-aed2-4ba077f4593a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace`, with `open OAI BitProgram StructuredCalls SubexpCRTOuterProgram`, `open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open DensePolynomialProgram ReconstructionProgram.Native`):
--
--   ```lean
--   theorem readback_run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t)
--       (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
--       (hcount : count < 3^t)
--       (hx : (RingProgram.modelRing t ht hd a M cache).decode x = (count : a.O t))
--       (regs : Fin 8 → Bool) (modulus width : List Bool)
--       (hm : BinaryArithmetic.toNat modulus = 3^t)
--       (hw : width.length = baseWidth 3 t)
--       (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : modulus.length ≤ S)
--       (hinput : (RingProgram.flat x).length ≤ S) :
--       ∃ finalRegs word steps, BinaryArithmetic.toNat word = count ∧
--         word.length = modulus.length + baseWidth 3 t ∧ steps ≤ 500*(S+1)^2 ∧
--         Trace LeafProgram.Readback.countProgram steps
--           ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
--             (some LeafProgram.Readback.countProgram.entry))
--           (⟨none, finalRegs, SubexpFlatCount.store word modulus [] width⟩ : Cfg 8 8 _) ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ steps →
--           Trace LeafProgram.Readback.countProgram prefixSteps
--             ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
--               (some LeafProgram.Readback.countProgram.entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             stackBits (SubexpFlatCount.start regs modulus width (RingProgram.flat x)).stacks +
--               500*(S+1)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.stackBits` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpFlatCount.store` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpFlatCount.start` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Readback.countCommand` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Readback.countProgram` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S100

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace

open OAI BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram ReconstructionProgram.Native

theorem readback_run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd a M cache).decode x = (count : a.O t))
    (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t)
    (hw : width.length = baseWidth 3 t)
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : modulus.length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ finalRegs word steps, BinaryArithmetic.toNat word = count ∧
      word.length = modulus.length + baseWidth 3 t ∧ steps ≤ 500*(S+1)^2 ∧
      Trace LeafProgram.Readback.countProgram steps
        ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
          (some LeafProgram.Readback.countProgram.entry))
        (⟨none, finalRegs, SubexpFlatCount.store word modulus [] width⟩ : Cfg 8 8 _) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace LeafProgram.Readback.countProgram prefixSteps
          ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
            (some LeafProgram.Readback.countProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits (SubexpFlatCount.start regs modulus width (RingProgram.flat x)).stacks +
            500*(S+1)^2 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
end
