-- Prove2me | Theorems.Thm_GlobalTheory_exists_finset_leftTransversal_of_relIndex_ne_zero
-- name    : GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:05.074072+00:00
-- url     : https://prove2.me/theorems/846f8f82-9a11-45f5-ba6d-92e02191c826
-- title:
--   Global Theory: exists finset left Transversal of rel Index ne zero
-- statement:
--   The Global Theory construction uses the exists finset left Transversal of rel Index ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinsetLeftTransversalOfRelIndexNeZero.lean#L5-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinsetLeftTransversalOfRelIndexNeZero.lean#L5-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetLeftTransversalOfRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero : ∀ {G : Type} [Group G] (H K : Subgroup G),
    K ≤ H → K.relIndex H ≠ 0 → ∃ R : Finset G, (∀ r ∈ R, r ∈ H) ∧ ∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K := by sorry
