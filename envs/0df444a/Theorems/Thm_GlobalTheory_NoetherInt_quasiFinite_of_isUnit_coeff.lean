-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_quasiFinite_of_isUnit_coeff
-- name    : GlobalTheory.NoetherInt.quasiFinite_of_isUnit_coeff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:27.188936+00:00
-- url     : https://prove2.me/theorems/5fae16e5-d3ab-4332-9e5f-c3457ece7dc1
-- title:
--   Noether Int: quasi Finite of is Unit coeff
-- statement:
--   The Noether Int construction uses the quasi Finite of is Unit coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L55-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L55-L75

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
open Polynomial

theorem GlobalTheory.NoetherInt.quasiFinite_of_isUnit_coeff {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (t : T)
    (h : (eval₂RingHom φ t).QuasiFinite) (G : R[X]) (hG : eval₂ φ t G = 0) (k : ℕ)
    (hc : IsUnit (φ (G.coeff k))) : φ.QuasiFinite := by sorry
