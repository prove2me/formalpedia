-- Prove2me | Theorems.Thm_GlobalTheory_isIso_grCechMap
-- name    : GlobalTheory.isIso_grCechMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:03.483779+00:00
-- url     : https://prove2.me/theorems/f1467c88-51b0-4ff7-9078-129af2d7edfd
-- title:
--   Global Theory: is Iso gr Cech Map
-- statement:
--   The Global Theory construction uses the is Iso gr Cech Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L654-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L654-L659

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
variable (ι : Type) {R : Type u} [CommRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type u} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]
variable {ι}
variable {ℳ}
variable [LinearOrder ι]

theorem GlobalTheory.isIso_grCechMap [Decomposition ℳ] [Decomposition 𝒩] {f : M →ₗ[MvPolynomial ι R] N}
    (hf : IsGradedMap ℳ 𝒩 f)
    (h₁ : ∀ (i : ι) m, f m = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • m = 0)
    (h₂ : ∀ (i : ι) y, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    IsIso (grCechMap hf n) := by sorry
