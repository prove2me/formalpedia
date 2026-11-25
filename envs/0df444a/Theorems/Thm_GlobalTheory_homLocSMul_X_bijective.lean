-- Prove2me | Theorems.Thm_GlobalTheory_homLocSMul_X_bijective
-- name    : GlobalTheory.homLocSMul_X_bijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:29.601375+00:00
-- url     : https://prove2.me/theorems/c533014b-fdfc-4efd-92f1-c19b24ef4bcc
-- title:
--   Global Theory: hom Loc SMul X bijective
-- statement:
--   The Global Theory construction uses the hom Loc SMul X bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L365-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L365-L367

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_X_mem_polyGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial CategoryTheory
universe u
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
variable (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]

theorem GlobalTheory.homLocSMul_X_bijective [Decomposition ℳ] {s : Finset ι} {i : ι} (hi : i ∈ s) (n : ℤ) :
    Function.Bijective (homLocSMul ℳ (X_mem_polyGrading i) s n) := by sorry
