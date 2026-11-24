-- Prove2me | Theorems.Thm_GlobalTheory_IsGradedMap_codRestrict
-- name    : GlobalTheory.IsGradedMap.codRestrict
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:13.208793+00:00
-- url     : https://prove2.me/theorems/19f21627-b9c8-47e1-95b7-5e4ff316175d
-- title:
--   Is Graded Map: cod Restrict
-- statement:
--   The Is Graded Map construction uses the cod Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L347-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L347-L349

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
omit [IsScalarTower R (MvPolynomial ι R) M]

theorem GlobalTheory.IsGradedMap.codRestrict {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (K : Submodule (MvPolynomial ι R) N)
    (h : ∀ m, f m ∈ K) : IsGradedMap ℳ (grSub 𝒩 K) (f.codRestrict K h) := by sorry
