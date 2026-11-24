-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuadraticUnit_isUnit_add_mul
-- name    : GlobalTheory.CompanionTheory.QuadraticUnit.isUnit_add_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:11.553074+00:00
-- url     : https://prove2.me/theorems/47f0c4fc-8ec2-47ae-9dc1-fc07216162cc
-- title:
--   Quadratic Unit: is Unit add mul
-- statement:
--   The Quadratic Unit construction uses the is Unit add mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipal.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipal.lean#L50-L59

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

theorem GlobalTheory.CompanionTheory.QuadraticUnit.isUnit_add_mul {R O : Type} [CommRing R] [HenselianLocalRing R] [CommRing O]
    (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (ι a + ι b * δ) := by sorry
