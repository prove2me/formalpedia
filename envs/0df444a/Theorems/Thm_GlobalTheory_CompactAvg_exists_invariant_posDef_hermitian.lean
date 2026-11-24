-- Prove2me | Theorems.Thm_GlobalTheory_CompactAvg_exists_invariant_posDef_hermitian
-- name    : GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:16:41.878071+00:00
-- url     : https://prove2.me/theorems/f3679026-5664-4363-af06-ead24921cc87
-- title:
--   Compact Avg: exists invariant pos Def hermitian
-- statement:
--   The Compact Avg construction uses the exists invariant pos Def hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInvariantPosDefHermitian.lean#L8-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInvariantPosDefHermitian.lean#L8-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantPosDefHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompactAvg
open MeasureTheory

theorem GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian {n : ℕ} (H : Subgroup (GL (Fin n) ℂ))
    (hH : IsCompact (H : Set (GL (Fin n) ℂ))) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by sorry
