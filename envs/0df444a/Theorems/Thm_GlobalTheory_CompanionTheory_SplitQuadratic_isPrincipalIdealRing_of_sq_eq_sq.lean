-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitQuadratic_isPrincipalIdealRing_of_sq_eq_sq
-- name    : GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:15:05.405082+00:00
-- url     : https://prove2.me/theorems/ca927031-9fad-4cca-9659-7f65300309f8
-- title:
--   Split Quadratic: is Principal Ideal Ring of sq eq sq
-- statement:
--   The Split Quadratic construction uses the is Principal Ideal Ring of sq eq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitQuadraticOrderPrincipal.lean#L5-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitQuadraticOrderPrincipal.lean#L5-L59

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitQuadraticOrderPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitQuadratic

theorem GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
      (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) →
      (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by sorry
