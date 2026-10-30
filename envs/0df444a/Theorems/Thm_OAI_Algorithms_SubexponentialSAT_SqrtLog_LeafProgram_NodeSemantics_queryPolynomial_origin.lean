-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeSemantics_queryPolynomial_origin
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:54:34.553444+00:00
-- url     : https://prove2.me/theorems/a2c8624c-7017-48d6-bdcf-e777b273b5a1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeSemanticsCount.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeSemanticsCount.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics`, with `open scoped BigOperators`, `open Polynomial`):
--
--   ```lean
--   theorem queryPolynomial_origin (rho : R →+* K) (q : R) (t : ℕ) (hq : q^t=0)
--       (hker : ∀ y, rho y=0 → q∣y) (digits : Fin t → R[X])
--       (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
--       (path : ℕ → V → R[X]) (x : V → Bool)
--       (hpath : ∀ i v, (path i v).eval 0 = HashInput.boolValue (x v))
--       (hres : ∀ i, rho (sourceHash hashes x i)=0 ∨ rho (sourceHash hashes x i)=1 ∨
--         rho (sourceHash hashes x i)=2)
--       (hdigit : ∀ i, (∑ s : Fin t, (digits s).eval (sourceHash hashes x i) *
--         IdempotentProgram.hValue (sourceHash hashes x i)^s.val) =
--           if rho (sourceHash hashes x i)=0 then 1 else 0) :
--       (queryPolynomial t digits hashes marked clause path).eval 0 =
--         if accepted rho hashes marked clause x then 1 else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput.boolValue` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.hValue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SparseRow` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.sourceHash` (definitions bundle `OAIQ081S076` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeSemanticsCount.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S076

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section
attribute [local instance] Classical.propDecidable

variable {R K : Type*} [CommRing R] [CommRing K] [DecidableEq K]
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem queryPolynomial_origin (rho : R →+* K) (q : R) (t : ℕ) (hq : q^t=0)
    (hker : ∀ y, rho y=0 → q∣y) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) (x : V → Bool)
    (hpath : ∀ i v, (path i v).eval 0 = HashInput.boolValue (x v))
    (hres : ∀ i, rho (sourceHash hashes x i)=0 ∨ rho (sourceHash hashes x i)=1 ∨
      rho (sourceHash hashes x i)=2)
    (hdigit : ∀ i, (∑ s : Fin t, (digits s).eval (sourceHash hashes x i) *
      IdempotentProgram.hValue (sourceHash hashes x i)^s.val) =
        if rho (sourceHash hashes x i)=0 then 1 else 0) :
    (queryPolynomial t digits hashes marked clause path).eval 0 =
      if accepted rho hashes marked clause x then 1 else 0 := by
  sorry

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end
