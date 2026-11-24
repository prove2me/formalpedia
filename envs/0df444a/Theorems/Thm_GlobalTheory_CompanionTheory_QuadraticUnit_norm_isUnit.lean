-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuadraticUnit_norm_isUnit
-- name    : GlobalTheory.CompanionTheory.QuadraticUnit.norm_isUnit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:20.453482+00:00
-- url     : https://prove2.me/theorems/2ef6df28-5681-4a68-bddb-cef2ac4641d1
-- title:
--   Quadratic Unit: norm is Unit
-- statement:
--   The Quadratic Unit construction uses the norm is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipal.lean#L7-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedQuadraticOrderPrincipal.lean#L7-L48

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

theorem GlobalTheory.CompanionTheory.QuadraticUnit.norm_isUnit {R : Type} [CommRing R] [HenselianLocalRing R] (D : R) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (a * a - D * (b * b)) := by sorry
