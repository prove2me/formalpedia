-- Prove2me | Theorems.Thm_GlobalTheory_dixmier_schur_of_rank_le_aleph0
-- name    : GlobalTheory.dixmier_schur_of_rank_le_aleph0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:49.468028+00:00
-- url     : https://prove2.me/theorems/4b6f7d7c-b908-4659-bf9f-d51d45f4644e
-- title:
--   Global Theory: dixmier schur of rank le aleph0
-- statement:
--   The Global Theory construction uses the dixmier schur of rank le aleph0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierSchurOfRankLeAleph0.lean#L57-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierSchurOfRankLeAleph0.lean#L57-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierSchurOfRankLeAleph0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.dixmier_schur_of_rank_le_aleph0 :
    ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V),
      Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
      (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by sorry
