-- Prove2me | Theorems.Thm_GlobalTheory_dualV_pairing_exists
-- name    : GlobalTheory.dualV_pairing_exists
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:40.085316+00:00
-- url     : https://prove2.me/theorems/df357161-76cf-42fb-84d4-e173c930b2b9
-- title:
--   Global Theory: dual V pairing exists
-- statement:
--   The Global Theory construction uses the dual V pairing exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMemPairingEqSingleNonradical.lean#L6-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMemPairingEqSingleNonradical.lean#L6-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMemPairingEqSingleNonradical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.dualV_pairing_exists : ∀ (r g rk : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)) (ε : Fin g → Fin r → ℚ), Mqᵀ = -Mq → LinearIndependent ℚ ε → (∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0) → (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → y ∈ Submodule.span ℚ (ε '' {i | i.val < rk})) → ∀ j : Fin g, rk ≤ j.val → ∃ x ∈ V, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by sorry
