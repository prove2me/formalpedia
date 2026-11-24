-- Prove2me | Theorems.Thm_GlobalTheory_IsIntegralDetLattice_isIntegral_of_isRoot_charpoly
-- name    : GlobalTheory.IsIntegralDetLattice.isIntegral_of_isRoot_charpoly
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:08.524268+00:00
-- url     : https://prove2.me/theorems/2d866350-50bc-48e8-a9f5-82584db2e225
-- title:
--   Is Integral Det Lattice: is Integral of is Root charpoly
-- statement:
--   The Is Integral Det Lattice construction uses the is Integral of is Root charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralDetOfPreservesLattice.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralDetOfPreservesLattice.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegralDetOfPreservesLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IsIntegralDetLattice

theorem GlobalTheory.IsIntegralDetLattice.isIntegral_of_isRoot_charpoly {R K : Type} [CommRing R] [Field K] [Algebra R K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (hA : IsIntegral R A) (x : K) (hx : A.charpoly.IsRoot x) :
    IsIntegral R x := by sorry
