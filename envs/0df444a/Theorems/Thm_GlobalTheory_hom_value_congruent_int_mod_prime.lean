-- Prove2me | Theorems.Thm_GlobalTheory_hom_value_congruent_int_mod_prime
-- name    : GlobalTheory.hom_value_congruent_int_mod_prime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:02.881036+00:00
-- url     : https://prove2.me/theorems/f871982f-c1d0-4abe-8f4a-31beb368997c
-- title:
--   Global Theory: hom value congruent int mod prime
-- statement:
--   The Global Theory construction uses the hom value congruent int mod prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HomValueCongruentIntModPrime.lean#L24-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HomValueCongruentIntModPrime.lean#L24-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HomValueCongruentIntModPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.hom_value_congruent_int_mod_prime :
    ∀ (A O : Type) [CommRing A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (σ : A →+* O) (x : A), (∃ i : ℤ, σ x - (i : O) ∈ Ideal.span {(g : O)}) ∧ (¬ IsUnit (σ x) → σ x ∈ Ideal.span {(g : O)}) := by sorry
