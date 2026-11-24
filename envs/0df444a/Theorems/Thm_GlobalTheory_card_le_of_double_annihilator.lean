-- Prove2me | Theorems.Thm_GlobalTheory_card_le_of_double_annihilator
-- name    : GlobalTheory.card_le_of_double_annihilator
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:04.652643+00:00
-- url     : https://prove2.me/theorems/29a8ebfa-db11-4c77-ac73-4ab72613ffe1
-- title:
--   Global Theory: card le of double annihilator
-- statement:
--   The Global Theory construction uses the card le of double annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardLeOfDoubleAnnihilatorPairing.lean#L5-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardLeOfDoubleAnnihilatorPairing.lean#L5-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardLeOfDoubleAnnihilatorPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.card_le_of_double_annihilator (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X]
    [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X]
    (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O)
    (h1 : ∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S)
    (h2 : ∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0)
    (h3 : ∀ e : E, a • e = 0 → e ∈ Es) :
    Nat.card X ≤ Es.card ^ F.card * Nat.card S := by sorry
