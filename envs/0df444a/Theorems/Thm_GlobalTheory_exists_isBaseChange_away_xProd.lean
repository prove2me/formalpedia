-- Prove2me | Theorems.Thm_GlobalTheory_exists_isBaseChange_away_xProd
-- name    : GlobalTheory.exists_isBaseChange_away_xProd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:59.718346+00:00
-- url     : https://prove2.me/theorems/ed5fad69-7217-45af-8880-9bcecda405ab
-- title:
--   Global Theory: exists is Base Change away x Prod
-- statement:
--   The Global Theory construction uses the exists is Base Change away x Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsBaseChangeAwayOfIntertwine.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsBaseChangeAwayOfIntertwine.lean#L95-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory

theorem GlobalTheory.exists_isBaseChange_away_xProd :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (s : Finset ι), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → ∃ θ : LocalizedModule.Away (xProd R₀ s) N₀ →ₗ[R₀] LocalizedModule.Away (xProd R s) N, IsBaseChange R θ ∧ ∀ (k : ℕ) y, θ (awayFrac N₀ (xProd R₀ s) k y) = awayFrac N (xProd R s) k (ψ y) := by sorry
