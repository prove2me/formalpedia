-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuadraticUnit_isPrincipalIdealRing_of_nonsquare_unit
-- name    : GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:13.917801+00:00
-- url     : https://prove2.me/theorems/8283efc8-5ac9-42d7-ad7f-bef59f228839
-- title:
--   Quadratic Unit: is Principal Ideal Ring of nonsquare unit
-- statement:
--   The Quadratic Unit construction uses the is Principal Ideal Ring of nonsquare unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipal.lean#L73-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipal.lean#L73-L98

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuadraticUnit
open Polynomial IsLocalRing

theorem GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
      [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by sorry
