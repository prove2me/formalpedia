-- Prove2me | Theorems.Thm_GlobalTheory_T_gram_det_eq_sq_mul_gram_det_of_mem_span
-- name    : GlobalTheory.T.gram_det_eq_sq_mul_gram_det_of_mem_span
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:51.16999+00:00
-- url     : https://prove2.me/theorems/5f85c399-41fa-55e8-8e90-7af880025bd7
-- title:
--   T: gram det eq sq mul gram det of mem span
-- statement:
--   The T construction uses the gram det eq sq mul gram det of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramDetIndexSublatticeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramDetIndexSublatticeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramDetIndexSublattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramDetIndexSublatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gram_det_eq_sq_mul_gram_det_of_mem_span : ∀ (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U), Fintype.card ι = Fintype.card κ → (∀ k, v k ∈ Submodule.span ℤ (Set.range u)) → ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧ ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by sorry
