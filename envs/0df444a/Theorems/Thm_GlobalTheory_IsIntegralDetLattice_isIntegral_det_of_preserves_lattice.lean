-- Prove2me | Theorems.Thm_GlobalTheory_IsIntegralDetLattice_isIntegral_det_of_preserves_lattice
-- name    : GlobalTheory.IsIntegralDetLattice.isIntegral_det_of_preserves_lattice
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:03.944994+00:00
-- url     : https://prove2.me/theorems/dd4856b1-e464-4110-a4ae-f14bf5e1248f
-- title:
--   Is Integral Det Lattice: is Integral det of preserves lattice
-- statement:
--   The Is Integral Det Lattice construction uses the is Integral det of preserves lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralDetOfPreservesLattice.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralDetOfPreservesLattice.lean#L64-L68

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

theorem GlobalTheory.IsIntegralDetLattice.isIntegral_det_of_preserves_lattice {E : Type} [Field E] [NumberField E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det := by sorry
