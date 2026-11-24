-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_quasiFinite_quotient_of_isUnit_coeff
-- name    : GlobalTheory.NoetherInt.quasiFinite_quotient_of_isUnit_coeff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:24.777172+00:00
-- url     : https://prove2.me/theorems/e5baf997-274b-4d32-bd7a-d20e2dfbfe56
-- title:
--   Noether Int: quasi Finite quotient of is Unit coeff
-- statement:
--   The Noether Int construction uses the quasi Finite quotient of is Unit coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L7-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L7-L34

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

theorem GlobalTheory.NoetherInt.quasiFinite_quotient_of_isUnit_coeff {R : Type*} [CommRing R] (G : R[X]) (k : ℕ)
    (hc : IsUnit (G.coeff k)) : Algebra.QuasiFinite R (R[X] ⧸ Ideal.span {G}) := by sorry
