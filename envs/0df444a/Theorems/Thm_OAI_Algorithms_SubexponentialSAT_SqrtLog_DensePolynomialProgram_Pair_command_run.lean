-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_Pair_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:27:48.146222+00:00
-- url     : https://prove2.me/theorems/b87391c1-1994-46ee-953d-e5fb034fe4f0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/DensePolynomialProgramPair.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/DensePolynomialProgramPair.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives`, `open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpConvolutionPair`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem command_run (hB : 0 < baseWidth p t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
--       (hadd : ∀ a b, (ops.addRun a b).1 =
--         (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
--       (hmul : ∀ a b, (ops.mulRun a b).1 =
--         (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
--       (s : Store) (a b c : Coeff (baseWidth p t) degree)
--       (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
--       (frame : Fin 6 → List Bool)
--       (H : Ready p t M cache table s a b c earlier rest widthWord indexWord scalarWidth frame) :
--       ExecutesIn command (budget degree (baseWidth p t) indexWord.length) s
--         (Function.update (Function.update (Function.update s 198 []) 199 []) 102
--           (earlier.flatten ++ (RingProgram.flat (ops.addRun (ops.mulRun a b).1 c).1 ++ rest)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.budget` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.addRun` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.mulRun` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command` (definitions bundle `OAIQ081S068` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.Ready` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/DensePolynomialProgramPair.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpConvolutionPair
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

theorem command_run (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (a b c : Coeff (baseWidth p t) degree)
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (H : Ready p t M cache table s a b c earlier rest widthWord indexWord scalarWidth frame) :
    ExecutesIn command (budget degree (baseWidth p t) indexWord.length) s
      (Function.update (Function.update (Function.update s 198 []) 199 []) 102
        (earlier.flatten ++ (RingProgram.flat (ops.addRun (ops.mulRun a b).1 c).1 ++ rest))) := by
  sorry

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair

end OAI.Algorithms
end
