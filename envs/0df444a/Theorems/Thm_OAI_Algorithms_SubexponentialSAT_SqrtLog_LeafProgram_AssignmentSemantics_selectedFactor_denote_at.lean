-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_AssignmentSemantics_selectedFactor_denote_at
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:26:45.782607+00:00
-- url     : https://prove2.me/theorems/6b944527-be09-429d-830a-4c4da9505960
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramAssignmentSemanticsSelected.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramAssignmentSemanticsSelected.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics`, with `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open HashCircuitProgram HashCircuitProgram.Native NativeSemantics`, `open IdempotentApplyProgram.Steps (Context)`, `open scoped BigOperators`):
--
--   ```lean
--   theorem selectedFactor_denote_at (ctx : Context p t n d)
--       (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
--       (htable : ∀ i j, basis i*basis j =
--         ∑ k, scalar (wordValue p t (ctx.table i j k))*basis k)
--       (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
--       (vars : Finset (Fin n))
--       (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
--       (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
--       (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
--         scalar basis minus = -1)
--       (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
--         scalar basis) one = Squarefree.canonical ctx.u ctx.J 1)
--       (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
--       (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
--       (marked : Bool) (clause : List (SAT.Literal (Fin n)))
--       (id : ℕ)
--       (hhash : ∀ (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
--         rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
--           scalar basis) (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J (jet id l.variable))
--       (hmark : marked=true → id=hashes.length → ∀ l ∈ clause,
--         rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
--           scalar basis) (incidence id l.variable) =
--             Squarefree.canonical ctx.u ctx.J (jet id l.variable))
--       (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (hfactor : selectedFactor ctx minus one incidence hashes marked clause
--         (List.ofFn (IdempotentApplyProgram.coefficientTriple t code)) id = some factor) :
--       rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
--         scalar basis) factor = Squarefree.canonical ctx.u ctx.J
--           (selectedValue ctx scalar basis code jet hashes marked clause id)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.wordValue` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.denote` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.coefficientTriple` (definitions bundle `OAIQ081S052` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarRing` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.Good` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.rawDenote` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedValue` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.hash_step_value` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.marked_step_value` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramAssignmentSemanticsSelected.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators
variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

theorem selectedFactor_denote_at (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) one = Squarefree.canonical ctx.u ctx.J 1)
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (id : ℕ)
    (hhash : ∀ (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J (jet id l.variable))
    (hmark : marked=true → id=hashes.length → ∀ l ∈ clause,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence id l.variable) =
          Squarefree.canonical ctx.u ctx.J (jet id l.variable))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hfactor : selectedFactor ctx minus one incidence hashes marked clause
      (List.ofFn (IdempotentApplyProgram.coefficientTriple t code)) id = some factor) :
    rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) factor = Squarefree.canonical ctx.u ctx.J
        (selectedValue ctx scalar basis code jet hashes marked clause id) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
end
