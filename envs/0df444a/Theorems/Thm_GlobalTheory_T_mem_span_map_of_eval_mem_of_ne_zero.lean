-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_span_map_of_eval_mem_of_ne_zero
-- name    : GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:52:52.140105+00:00
-- url     : https://prove2.me/theorems/fcbb1309-10ae-4011-8d03-febd11734905
-- title:
--   T: mem span map of eval mem of ne zero
-- statement:
--   The T construction uses the mem span map of eval mem of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemSpanMapOfEvalMemOfNeZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemSpanMapOfEvalMemOfNeZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MemSpanMapOfEvalMemOfNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MemSpanMapOfEvalMemOfNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero : ∀ (k : Type) [Field k] [Infinite k] (σ τ : Type) (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k), D ≠ 0 → ∀ P : MvPolynomial σ (MvPolynomial τ k), (∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) → P ∈ Submodule.span (MvPolynomial τ k) (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by sorry
