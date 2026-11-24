-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_map_of_eval_mem
-- name    : GlobalTheory.mem_span_map_of_eval_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:14.764484+00:00
-- url     : https://prove2.me/theorems/7463aa5f-f464-4848-95c7-36754b1660a4
-- title:
--   Global Theory: mem span map of eval mem
-- statement:
--   The Global Theory construction uses the mem span map of eval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemSpanMapOfEvalMemOfNeZero.lean#L6-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemSpanMapOfEvalMemOfNeZero.lean#L6-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MemSpanMapOfEvalMemOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem GlobalTheory.mem_span_map_of_eval_mem (k : Type) [Field k] [Infinite k] (σ τ : Type)
    (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k) (hD : D ≠ 0)
    (P : MvPolynomial σ (MvPolynomial τ k))
    (hP : ∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) :
    P ∈ Submodule.span (MvPolynomial τ k)
      (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by sorry
