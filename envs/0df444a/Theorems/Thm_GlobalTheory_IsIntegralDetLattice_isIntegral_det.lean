-- Prove2me | Theorems.Thm_GlobalTheory_IsIntegralDetLattice_isIntegral_det
-- name    : GlobalTheory.IsIntegralDetLattice.isIntegral_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:37.646927+00:00
-- url     : https://prove2.me/theorems/23f5ee99-ccce-4d2e-8f72-b77d84b20758
-- title:
--   Is Integral Det Lattice: is Integral det
-- statement:
--   The Is Integral Det Lattice construction uses the is Integral det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralDetOfPreservesLattice.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralDetOfPreservesLattice.lean#L20-L32

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

theorem GlobalTheory.IsIntegralDetLattice.isIntegral_det {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) E) (hA : IsIntegral R A) : IsIntegral R A.det := by sorry
