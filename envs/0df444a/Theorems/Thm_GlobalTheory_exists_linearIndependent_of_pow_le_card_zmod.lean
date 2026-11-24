-- Prove2me | Theorems.Thm_GlobalTheory_exists_linearIndependent_of_pow_le_card_zmod
-- name    : GlobalTheory.exists_linearIndependent_of_pow_le_card_zmod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:15.525746+00:00
-- url     : https://prove2.me/theorems/092dd1e6-f23c-4a57-ab67-1096390bb950
-- title:
--   Global Theory: exists linear Independent of pow le card zmod
-- statement:
--   The Global Theory construction uses the exists linear Independent of pow le card zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIndependentModPrimeOfPowLeCard.lean#L6-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIndependentModPrimeOfPowLeCard.lean#L6-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIndependentModPrimeOfPowLeCard
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

theorem GlobalTheory.exists_linearIndependent_of_pow_le_card_zmod (l : ℕ) [Fact l.Prime] {Q ι : Type} [AddCommGroup Q] [Module (ZMod l) Q]
    (Z : Finset ι) (w : ι → Q) (hinj : Set.InjOn w Z) (h : ℕ) (hcard : l ^ h ≤ Z.card) :
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ LinearIndependent (ZMod l) (fun a => w (x a)) := by sorry
