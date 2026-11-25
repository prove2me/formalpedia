-- Prove2me | Theorems.Thm_GlobalTheory_T_flat_of_local_retractions_mod_maximalIdeal_pow
-- name    : GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:33.368897+00:00
-- url     : https://prove2.me/theorems/20f3955c-5521-4f33-b4ff-74eacb5b1912
-- title:
--   T: flat of local retractions mod maximal Ideal pow
-- statement:
--   The T construction uses the flat of local retractions mod maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatOfLocalRetractionsModMaximalIdealPowStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatOfLocalRetractionsModMaximalIdealPowStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatOfLocalRetractionsModMaximalIdealPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatOfLocalRetractionsModMaximalIdealPowStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow : ∀ {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ], (∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _) → (∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) → φ.Flat := by sorry
