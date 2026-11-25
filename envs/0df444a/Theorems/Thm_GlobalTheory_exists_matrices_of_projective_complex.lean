-- Prove2me | Theorems.Thm_GlobalTheory_exists_matrices_of_projective_complex
-- name    : GlobalTheory.exists_matrices_of_projective_complex
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:32.817923+00:00
-- url     : https://prove2.me/theorems/c81fb57e-cfc3-4558-ab6e-3527e277b970
-- title:
--   Global Theory: exists matrices of projective complex
-- statement:
--   The Global Theory construction uses the exists matrices of projective complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMatricesOfProjectiveComplex.lean#L90-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMatricesOfProjectiveComplex.lean#L90-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMatricesOfProjectiveComplex
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

theorem GlobalTheory.exists_matrices_of_projective_complex :
    ∀ (R : Type) [CommRing R] (P₀ P₁ P₂ : Type) [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₀] [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (d₀ : P₀ →ₗ[R] P₁) (d₁ : P₁ →ₗ[R] P₂), d₁ ∘ₗ d₀ = 0 → ∃ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R) (u : Fin a → P₀), D₁ * D₀ = 0 ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], Set.BijOn (fun v : Fin a → R' => ∑ k, v k ⊗ₜ[R] u k) {v | (D₀.map (algebraMap R R')).mulVec v = 0} (LinearMap.ker (d₀.baseChange R')) ∧ (Function.Exact (d₀.baseChange R') (d₁.baseChange R') → ∀ w : Fin b → R', (D₁.map (algebraMap R R')).mulVec w = 0 → ∃ v, (D₀.map (algebraMap R R')).mulVec v = w) := by sorry
