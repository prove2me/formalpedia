-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_posDef_hermitian_invariant_of_isCompact
-- name    : GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:28.790025+00:00
-- url     : https://prove2.me/theorems/317d1d03-57e2-43eb-97e6-92f43b983606
-- title:
--   T: exists pos Def hermitian invariant of is Compact
-- statement:
--   The T construction uses the exists pos Def hermitian invariant of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInvariantPosDefHermitianStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInvariantPosDefHermitianStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantPosDefHermitian
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantPosDefHermitianStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact : ∀ {n : ℕ} (H : Subgroup (GL (Fin n) ℂ)), IsCompact (H : Set (GL (Fin n) ℂ)) →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by sorry
