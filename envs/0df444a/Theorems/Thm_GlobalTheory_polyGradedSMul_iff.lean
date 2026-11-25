-- Prove2me | Theorems.Thm_GlobalTheory_polyGradedSMul_iff
-- name    : GlobalTheory.polyGradedSMul_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:49:16.477594+00:00
-- url     : https://prove2.me/theorems/6f46b3f0-609a-5484-bd2e-7ab208d69f73
-- title:
--   Global Theory: poly Graded SMul iff
-- statement:
--   The Global Theory construction uses the poly Graded SMul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L119-L122

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

theorem GlobalTheory.polyGradedSMul_iff [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) :
    PolyGradedSMul ι ℳ ↔
      ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (X i : MvPolynomial ι R) • m ∈ ℳ (n + 1) := by sorry
