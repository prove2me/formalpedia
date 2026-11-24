-- Prove2me | Theorems.Thm_GlobalTheory_IsIntegralDetLattice_isIntegral_of_preserves
-- name    : GlobalTheory.IsIntegralDetLattice.isIntegral_of_preserves
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:07.776366+00:00
-- url     : https://prove2.me/theorems/d4557d04-f1c5-4876-9738-cc8ab40242d4
-- title:
--   Is Integral Det Lattice: is Integral of preserves
-- statement:
--   The Is Integral Det Lattice construction uses the is Integral of preserves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralDetOfPreservesLattice.lean#L34-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralDetOfPreservesLattice.lean#L34-L62

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

theorem GlobalTheory.IsIntegralDetLattice.isIntegral_of_preserves {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (L : Submodule R (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ := by sorry
