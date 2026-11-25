-- Prove2me | Theorems.Thm_GlobalTheory_exists_homogeneous_family_saturating
-- name    : GlobalTheory.exists_homogeneous_family_saturating
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:40.617106+00:00
-- url     : https://prove2.me/theorems/4b333787-463c-472a-8230-86706849912c
-- title:
--   Global Theory: exists homogeneous family saturating
-- statement:
--   The Global Theory construction uses the exists homogeneous family saturating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsHomogeneousFamilySaturating.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsHomogeneousFamilySaturating.lean#L9-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomogeneousFamilySaturating
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
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct

theorem GlobalTheory.exists_homogeneous_family_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ], (∀ i : ι, ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M)) → ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) ∧ ∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by sorry
