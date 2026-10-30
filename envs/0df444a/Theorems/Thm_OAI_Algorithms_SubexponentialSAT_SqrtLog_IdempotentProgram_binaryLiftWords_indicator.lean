-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentProgram_binaryLiftWords_indicator
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:30:15.147023+00:00
-- url     : https://prove2.me/theorems/880458fe-e041-419c-8fbf-1ad7607aa1d9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentProgramFinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentProgramFinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram`, with `open scoped BigOperators`, `open BitProgram StructuredCalls SubexpSymbolicCost`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem binaryLiftWords_indicator [DecidableEq K]
--       (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
--       (hu : 2*wordValue 3 t u = 1)
--       (φ : ZMod (3^t) →+* R) (ρ : R →+* K)
--       (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
--       (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
--       (∑ s : Fin t,
--         (digitPolynomial (RingProgram.scalarRing 3 t M cache)
--           (binaryLiftWords t M cache u) s).eval₂ φ x * hValue x^s.val) =
--         if ρ x = 0 then 1 else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.hValue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.ternaryPrimeFinal` (definitions bundle `OAIQ081S010` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` and `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.wordValue` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.digitPolynomial` (definitions bundle `OAIQ081S070` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarRing` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords` (definitions bundle `OAIQ081S121` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentProgramFinal.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator)

import Mathlib
import Definitions.Def_OAIQ081S121

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {R K : Type*} [CommRing R] [CommRing K]

attribute [local instance] OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.ternaryPrimeFinal
theorem binaryLiftWords_indicator [DecidableEq K]
    (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (hu : 2*wordValue 3 t u = 1)
    (φ : ZMod (3^t) →+* R) (ρ : R →+* K)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    (∑ s : Fin t,
      (digitPolynomial (RingProgram.scalarRing 3 t M cache)
        (binaryLiftWords t M cache u) s).eval₂ φ x * hValue x^s.val) =
      if ρ x = 0 then 1 else 0 := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end
