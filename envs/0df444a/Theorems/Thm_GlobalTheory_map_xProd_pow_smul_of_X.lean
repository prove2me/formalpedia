-- Prove2me | Theorems.Thm_GlobalTheory_map_xProd_pow_smul_of_X
-- name    : GlobalTheory.map_xProd_pow_smul_of_X
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:21.520165+00:00
-- url     : https://prove2.me/theorems/aa7f30e8-972b-44f1-8e3a-678fd3d89f01
-- title:
--   Global Theory: map x Prod pow smul of X
-- statement:
--   The Global Theory construction uses the map x Prod pow smul of X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBaseChangeGrCubeIso.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBaseChangeGrCubeIso.lean#L10-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeGradedPiece
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBaseChangeGrCubeIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory

theorem GlobalTheory.map_xProd_pow_smul_of_X {ι R₀ R : Type} [CommRing R₀] [CommRing R] {N₀ N : Type}
    [AddCommGroup N₀] [Module (MvPolynomial ι R₀) N₀] [AddCommGroup N]
    [Module (MvPolynomial ι R) N] (ψ : N₀ → N)
    (hX : ∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y)
    (s : Finset ι) (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by sorry
