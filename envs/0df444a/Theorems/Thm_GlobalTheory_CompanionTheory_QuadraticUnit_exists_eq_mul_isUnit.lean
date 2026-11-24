-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuadraticUnit_exists_eq_mul_isUnit
-- name    : GlobalTheory.CompanionTheory.QuadraticUnit.exists_eq_mul_isUnit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:10.688451+00:00
-- url     : https://prove2.me/theorems/5707aacc-7a33-49c4-86af-7136f281f5ba
-- title:
--   Quadratic Unit: exists eq mul is Unit
-- statement:
--   The Quadratic Unit construction uses the exists eq mul is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipal.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipal.lean#L61-L71

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

theorem GlobalTheory.CompanionTheory.QuadraticUnit.exists_eq_mul_isUnit {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D)
    (hspan : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (y : O) :
    ∃ (g : R) (u : O), IsUnit u ∧ y = ι g * u := by sorry
