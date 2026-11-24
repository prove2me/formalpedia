-- Prove2me | Theorems.Thm_GlobalTheory_T_card_le_of_double_annihilator_pairing
-- name    : GlobalTheory.T.card_le_of_double_annihilator_pairing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:46.778942+00:00
-- url     : https://prove2.me/theorems/f9ab4488-f886-4b3c-b5d8-772f36b4f898
-- title:
--   T: card le of double annihilator pairing
-- statement:
--   The T construction uses the card le of double annihilator pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardLeOfDoubleAnnihilatorPairingStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardLeOfDoubleAnnihilatorPairingStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardLeOfDoubleAnnihilatorPairing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardLeOfDoubleAnnihilatorPairingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_le_of_double_annihilator_pairing : ∀ (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X] (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O), (∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S) → (∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0) → (∀ e : E, a • e = 0 → e ∈ Es) → Nat.card X ≤ Es.card ^ F.card * Nat.card S := by sorry
