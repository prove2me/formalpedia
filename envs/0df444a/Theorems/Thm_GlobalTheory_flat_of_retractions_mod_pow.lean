-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_retractions_mod_pow
-- name    : GlobalTheory.flat_of_retractions_mod_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:52:37.474159+00:00
-- url     : https://prove2.me/theorems/ca8d0708-5cee-4a38-aca0-1701985b3d4b
-- title:
--   Global Theory: flat of retractions mod pow
-- statement:
--   The Global Theory construction uses the flat of retractions mod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatOfLocalRetractionsModMaximalIdealPow.lean#L67-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatOfLocalRetractionsModMaximalIdealPow.lean#L67-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatOfLocalRetractionsModMaximalIdealPow
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.flat_of_retractions_mod_pow {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hex : ∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _)
    (huniq : ∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ →
      IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) : φ.Flat := by sorry
