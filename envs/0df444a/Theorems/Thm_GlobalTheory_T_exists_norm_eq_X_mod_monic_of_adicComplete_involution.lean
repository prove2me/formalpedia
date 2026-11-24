-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_norm_eq_X_mod_monic_of_adicComplete_involution
-- name    : GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:35.492435+00:00
-- url     : https://prove2.me/theorems/2acdcf12-5468-4243-8d46-b5491a06248f
-- title:
--   T: exists norm eq X mod monic of adic Complete involution
-- statement:
--   The T construction uses the exists norm eq X mod monic of adic Complete involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by sorry
