-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_descendingStored_denote
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:56:49.625444+00:00
-- url     : https://prove2.me/theorems/b8cfb170-9302-4d0c-a20d-2b8654b2ae95
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramStored.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramStored.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram`, with `open scoped BigOperators`, `open SubexpLiftRing SubexpQuarticRing`, `open MomentsProgram`):
--
--   ```lean
--   theorem descendingStored_denote
--       (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
--       (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
--       (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J)
--       (h g : Stored p t (n:=n) (d:=d)) (vs : List (Triple (RingProgram.ScalarCode p t)))
--       (acc : Stored p t (n:=n) (d:=d)) :
--       storedDenote p t M cache φ basis (descendingStored p t M cache table uCap J h g vs acc)=
--         descendingAlgebra (LeafProgram.projectedAlgebra (Squarefree.canonical (V:=Fin n) (R:=R) uCap J))
--           (fun c => Squarefree.canonical (V:=Fin n) (R:=R) uCap J
--             ((Moments.ringScalar (V:=Fin n)).comp φ (wordValue p t c)))
--           (storedDenote p t M cache φ basis h) (storedDenote p t M cache φ basis g)
--           vs (storedDenote p t M cache φ basis acc)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingAlgebra` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` and `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.wordValue` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.projectedAlgebra` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.ringScalar` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Stored`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.storedDenote` (definitions bundle `OAIQ081S139` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramStored.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote)

import Mathlib
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}

variable {R : Type*} [CommRing R] (φ : ZMod (p^t) →+* R) (basis : Fin d → R)

theorem descendingStored_denote
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J)
    (h g : Stored p t (n:=n) (d:=d)) (vs : List (Triple (RingProgram.ScalarCode p t)))
    (acc : Stored p t (n:=n) (d:=d)) :
    storedDenote p t M cache φ basis (descendingStored p t M cache table uCap J h g vs acc)=
      descendingAlgebra (LeafProgram.projectedAlgebra (Squarefree.canonical (V:=Fin n) (R:=R) uCap J))
        (fun c => Squarefree.canonical (V:=Fin n) (R:=R) uCap J
          ((Moments.ringScalar (V:=Fin n)).comp φ (wordValue p t c)))
        (storedDenote p t M cache φ basis h) (storedDenote p t M cache φ basis g)
        vs (storedDenote p t M cache φ basis acc) := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end
