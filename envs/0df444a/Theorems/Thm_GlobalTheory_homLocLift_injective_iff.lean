-- Prove2me | Theorems.Thm_GlobalTheory_homLocLift_injective_iff
-- name    : GlobalTheory.homLocLift_injective_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:54.883028+00:00
-- url     : https://prove2.me/theorems/39f5aea0-48fb-4d90-b3a7-22e2d52eddb3
-- title:
--   Global Theory: hom Loc Lift injective iff
-- statement:
--   The Global Theory construction uses the hom Loc Lift injective iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L502-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L502-L511

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
  [IsScalarTower R (MvPolynomial ι R) M] {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
  {T : Type*} [AddCommGroup T] [Module R T] {s : Finset ι} {n : ℤ}
  (φ : ∀ k : ℕ, ℳ (n + k * s.card) →ₗ[R] T)
  (hφ : ∀ (k : ℕ) (m : ℳ (n + k * s.card)) (m' : ℳ (n + (k + 1 : ℕ) * s.card)),
    (m' : M) = xProd R s • (m : M) → φ (k + 1) m' = φ k m)
include hφ

theorem GlobalTheory.homLocLift_injective_iff : Function.Injective (homLocLift φ hφ) ↔
    ∀ k m, φ k m = 0 → ∃ l : ℕ, xProd R s ^ l • (m : M) = 0 := by sorry
