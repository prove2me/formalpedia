-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_mem_pairing_eq_single_nonradical
-- name    : GlobalTheory.T.exists_mem_pairing_eq_single_nonradical
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:49.271091+00:00
-- url     : https://prove2.me/theorems/442bbfe4-088e-5bbd-84b1-e4575013fb4d
-- title:
--   T: exists mem pairing eq single nonradical
-- statement:
--   The T construction uses the exists mem pairing eq single nonradical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMemPairingEqSingleNonradicalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMemPairingEqSingleNonradicalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMemPairingEqSingleNonradical
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMemPairingEqSingleNonradicalStatement
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

theorem GlobalTheory.T.exists_mem_pairing_eq_single_nonradical : ∀ (r g rk : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)) (ε : Fin g → Fin r → ℚ), Mqᵀ = -Mq → LinearIndependent ℚ ε → (∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0) → (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → y ∈ Submodule.span ℚ (ε '' {i | i.val < rk})) → ∀ j : Fin g, rk ≤ j.val → ∃ x ∈ V, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by sorry
