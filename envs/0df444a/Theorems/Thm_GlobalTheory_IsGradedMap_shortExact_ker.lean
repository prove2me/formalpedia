-- Prove2me | Theorems.Thm_GlobalTheory_IsGradedMap_shortExact_ker
-- name    : GlobalTheory.IsGradedMap.shortExact_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:31.835799+00:00
-- url     : https://prove2.me/theorems/9e884c4b-cff4-4f2c-840f-84f146a3da8d
-- title:
--   Is Graded Map: short Exact ker
-- statement:
--   The Is Graded Map construction uses the short Exact ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L724-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L724-L727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
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
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) P]
omit [IsScalarTower R (MvPolynomial ι R) P]

theorem GlobalTheory.IsGradedMap.shortExact_ker {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}
    {g : N →ₗ[MvPolynomial ι R] P} (hg : IsGradedMap 𝒩 𝒬 g) (h : Function.Surjective g) :
    GradedShortExact (grSub 𝒩 (LinearMap.ker g)) 𝒩 𝒬 (LinearMap.ker g).subtype g := by sorry
