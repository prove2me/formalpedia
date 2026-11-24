-- Prove2me | Theorems.Thm_GlobalTheory_proj_smul_of_mem
-- name    : GlobalTheory.proj_smul_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:34.575535+00:00
-- url     : https://prove2.me/theorems/0e701a09-75a5-4f83-aeca-ea9068220679
-- title:
--   Global Theory: proj smul of mem
-- statement:
--   The Global Theory construction uses the proj smul of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L304-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L304-L308

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

theorem GlobalTheory.proj_smul_of_mem (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [PolyGradedSMul ι ℳ]
    {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) (n : ℤ) (m : M) :
    proj ℳ (n + d) (p • m) = p • proj ℳ n m := by sorry
