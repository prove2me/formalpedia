-- Prove2me | Theorems.Thm_GlobalTheory_gram_det_index_sublattice
-- name    : GlobalTheory.gram_det_index_sublattice
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:57.4748+00:00
-- url     : https://prove2.me/theorems/071a5867-6fce-4729-863c-260d6555b2b3
-- title:
--   Global Theory: gram det index sublattice
-- statement:
--   The Global Theory construction uses the gram det index sublattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramDetIndexSublattice.lean#L7-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramDetIndexSublattice.lean#L7-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramDetIndexSublattice
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
open GlobalTheory

theorem GlobalTheory.gram_det_index_sublattice (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U) (hc : Fintype.card ι = Fintype.card κ)
    (hv : ∀ k, v k ∈ Submodule.span ℤ (Set.range u)) :
    ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧
      ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by sorry
