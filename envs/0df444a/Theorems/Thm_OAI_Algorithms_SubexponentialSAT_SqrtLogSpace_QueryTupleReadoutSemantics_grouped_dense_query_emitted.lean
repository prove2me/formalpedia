-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTupleReadoutSemantics_grouped_dense_query_emitted
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:21:35.371991+00:00
-- url     : https://prove2.me/theorems/144fbd72-bfa1-4cef-aa55-b4345e765ca9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTupleReadoutSemantics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTupleReadoutSemantics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics`, with `open scoped BigOperators`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog Moments SignatureTupleDFS SignatureTupleTraversal`, `open Classical`):
--
--   ```lean
--   theorem grouped_dense_query_emitted (t J : ℕ) (head : V → Fin r)
--       (key : (i : ℕ) → Fin (count i) → K i)
--       (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ (Head head g → Bool))
--       (label : ∀ g, (Head head g → Bool) → L g)
--       (hkernel : ∀ g i j, key g.val i = key g.val j ↔
--         label g (enumerate g i) = label g (enumerate g j))
--       (A : Fin r → (V → Bool) → Squarefree.Jet V R)
--       (hadm : ∀ x, Squarefree.Admissible (∏ g, A g x))
--       (hlocal : ∀ (U : Finset V) g x z,
--         split head x g = split head z g →
--         (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
--         QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g x) =
--           QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g z)) :
--       Dense.readout (∑ x, QueryEvaluation.specializeDense t J x (∏ g, A g x)) =
--         ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
--           ((-1 : ℤ) ^ (E.card - U.card)) •
--             ∑ reps : Prefix (Representatives key) r,
--               Dense.readout (∏ g, ∑ a : Head head g → Bool,
--                 if label g a = label g (enumerate g (reps g).val) ∧
--                     (∀ v : Head head g, v.val ∈ E → a v = true) then
--                   QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U))
--                     (A g (assemble head
--                       (Function.update (fun h => enumerate h (reps h).val) g a)))
--                 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Head` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instZero` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS.Prefix` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.assemble`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.headDecidableEq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.headFintype` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.split` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Representatives` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Admissible` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense.readout`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation.specializeDense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommRing`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instSMulInt` (definitions bundle `OAIQ081S115` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTupleReadoutSemantics.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted)

import Mathlib
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog Moments SignatureTupleDFS SignatureTupleTraversal
open Classical

section Readout

variable {r : ℕ} {count : ℕ → ℕ} {K : ℕ → Type*}
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    {L : Fin r → Type*} [∀ g, DecidableEq (L g)]

theorem grouped_dense_query_emitted (t J : ℕ) (head : V → Fin r)
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ (Head head g → Bool))
    (label : ∀ g, (Head head g → Bool) → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (A : Fin r → (V → Bool) → Squarefree.Jet V R)
    (hadm : ∀ x, Squarefree.Admissible (∏ g, A g x))
    (hlocal : ∀ (U : Finset V) g x z,
      split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g x) =
        QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g z)) :
    Dense.readout (∑ x, QueryEvaluation.specializeDense t J x (∏ g, A g x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        ((-1 : ℤ) ^ (E.card - U.card)) •
          ∑ reps : Prefix (Representatives key) r,
            Dense.readout (∏ g, ∑ a : Head head g → Bool,
              if label g a = label g (enumerate g (reps g).val) ∧
                  (∀ v : Head head g, v.val ∈ E → a v = true) then
                QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U))
                  (A g (assemble head
                    (Function.update (fun h => enumerate h (reps h).val) g a)))
              else 0) := by
  sorry

end Readout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics
end
end
