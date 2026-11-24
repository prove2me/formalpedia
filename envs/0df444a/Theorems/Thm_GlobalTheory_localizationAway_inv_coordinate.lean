-- Prove2me | Theorems.Thm_GlobalTheory_localizationAway_inv_coordinate
-- name    : GlobalTheory.localizationAway_inv_coordinate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:57.788785+00:00
-- url     : https://prove2.me/theorems/3e3b4576-5e22-4c9b-9c71-aba00dbfa289
-- title:
--   Global Theory: localization Away inv coordinate
-- statement:
--   The Global Theory construction uses the localization Away inv coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInversionCoordinateLocalizationPolynomial.lean#L33-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInversionCoordinateLocalizationPolynomial.lean#L33-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomial
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

theorem GlobalTheory.localizationAway_inv_coordinate (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    ∃ Q : Polynomial k, Q ≠ 0 ∧
      ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q)
        (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)),
        (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) =
            algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧
          τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) =
            (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
              IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by sorry
