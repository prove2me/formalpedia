-- Prove2me | Theorems.Thm_GlobalTheory_IsGradedMap_exact_of_exact_piece
-- name    : GlobalTheory.IsGradedMap.exact_of_exact_piece
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:24.593262+00:00
-- url     : https://prove2.me/theorems/df953f72-6437-4efb-b082-e571082af968
-- title:
--   Is Graded Map: exact of exact piece
-- statement:
--   The Is Graded Map construction uses the exact of exact piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L220-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L220-L237

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
open GlobalTheory.IsGradedMap
variable {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) P]
variable [Decomposition ℳ] [Decomposition 𝒩]

theorem GlobalTheory.IsGradedMap.exact_of_exact_piece [Decomposition 𝒬] {f : M →ₗ[MvPolynomial ι R] N}
    {g : N →ₗ[MvPolynomial ι R] P} (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap 𝒩 𝒬 g)
    (h : ∀ n, Function.Exact (hf.piece n) (hg.piece n)) : Function.Exact f g := by sorry
