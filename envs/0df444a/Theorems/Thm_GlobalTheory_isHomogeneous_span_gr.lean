-- Prove2me | Theorems.Thm_GlobalTheory_isHomogeneous_span_gr
-- name    : GlobalTheory.isHomogeneous_span_gr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:57.801815+00:00
-- url     : https://prove2.me/theorems/3518955d-440f-4613-bb8a-7edd39b9a3f8
-- title:
--   Global Theory: is Homogeneous span gr
-- statement:
--   The Global Theory construction uses the is Homogeneous span gr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L413-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L413-L423

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

theorem GlobalTheory.isHomogeneous_span_gr (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [PolyGradedSMul ι ℳ]
    {G : Set M} (hG : ∀ g ∈ G, ∃ d, g ∈ ℳ d) :
    (Submodule.span (MvPolynomial ι R) G).IsHomogeneous ℳ := by sorry
