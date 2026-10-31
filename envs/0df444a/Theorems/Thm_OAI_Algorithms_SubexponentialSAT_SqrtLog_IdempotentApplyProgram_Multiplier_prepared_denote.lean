-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Multiplier_prepared_denote
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:54:47.131332+00:00
-- url     : https://prove2.me/theorems/5c577984-8856-4fb6-83f8-4da5603df515
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramMultiplierKernel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramMultiplierKernel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier`, with `open scoped BigOperators`, `open SubexpLiftRing SubexpQuarticRing`, `open MomentsProgram`, `open Steps`):
--
--   ```lean
--   theorem prepared_denote (c : Context p t n d) (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
--       (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (c.table i j k))*basis k)
--       (minus : RingProgram.Code (Word (baseWidth p t)) d)
--       (hminus : RingProgram.denote (RingProgram.scalarRing p t c.modulus c.cache) φ basis minus = -1)
--       (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (honeKeys : (Squarefree.Sparse.keys one).Nodup)
--       (hone : storedDenote p t c.modulus c.cache φ basis one=Squarefree.canonical c.u c.J 1)
--       (H : Squarefree.Jet (Fin n) R)
--       (hh : storedDenote p t c.modulus c.cache φ basis h=Squarefree.canonical c.u c.J H) :
--       storedDenote p t c.modulus c.cache φ basis (prepared c minus h one)=
--         Squarefree.canonical c.u c.J
--           (Squarefree.Sparse.atom (uKey n) 1 * IdempotentProgram.hValue H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Sparse.keys` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.hValue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.wordValue` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.denote` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Sparse.atom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.uKey` (definitions bundle `OAIQ081S052` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarRing` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.storedDenote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw` (definitions bundle `OAIQ081S139` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramMultiplierKernel.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote)

import Mathlib
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open scoped BigOperators
open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem prepared_denote (c : Context p t n d) (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (c.table i j k))*basis k)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t c.modulus c.cache) φ basis minus = -1)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (honeKeys : (Squarefree.Sparse.keys one).Nodup)
    (hone : storedDenote p t c.modulus c.cache φ basis one=Squarefree.canonical c.u c.J 1)
    (H : Squarefree.Jet (Fin n) R)
    (hh : storedDenote p t c.modulus c.cache φ basis h=Squarefree.canonical c.u c.J H) :
    storedDenote p t c.modulus c.cache φ basis (prepared c minus h one)=
      Squarefree.canonical c.u c.J
        (Squarefree.Sparse.atom (uKey n) 1 * IdempotentProgram.hValue H) := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

end OAI.Algorithms
end
