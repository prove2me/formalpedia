-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_baseChange_grCube_iso
-- name    : GlobalTheory.nonempty_baseChange_grCube_iso
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:15.92153+00:00
-- url     : https://prove2.me/theorems/1d7e2656-4d55-4d91-8285-1886708001fb
-- title:
--   Global Theory: nonempty base Change gr Cube iso
-- statement:
--   The Global Theory construction uses the nonempty base Change gr Cube iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBaseChangeGrCubeIso.lean#L26-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBaseChangeGrCubeIso.lean#L26-L56

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

theorem GlobalTheory.nonempty_baseChange_grCube_iso : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] (𝒩₀ : ℤ → Submodule R₀ N₀) [PolyGradedSMul ι 𝒩₀] [Decomposition 𝒩₀] (N : Type) [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩] [Decomposition 𝒩] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (n : ℤ), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → Nonempty (Cube.baseChange R (grCube ι 𝒩₀ n) ≅ grCube ι 𝒩 n) := by sorry
