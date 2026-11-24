-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_map_finSuccEquiv
-- name    : GlobalTheory.NoetherInt.map_finSuccEquiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:02.324826+00:00
-- url     : https://prove2.me/theorems/c9c80e61-1b3d-4e6a-9f93-c769b433ec84
-- title:
--   Noether Int: map fin Succ Equiv
-- statement:
--   The Noether Int construction uses the map fin Succ Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L114-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
variable {A : Type*} [CommRing A] {n : ℕ}

theorem GlobalTheory.NoetherInt.map_finSuccEquiv {B : Type*} [CommRing B] (φ : A →+* B)
    (h : MvPolynomial (Fin (n + 1)) A) :
    Polynomial.map (MvPolynomial.map φ) (finSuccEquiv A n h) =
      finSuccEquiv B n (MvPolynomial.map φ h) := by sorry
