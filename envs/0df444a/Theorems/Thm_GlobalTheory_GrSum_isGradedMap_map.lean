-- Prove2me | Theorems.Thm_GlobalTheory_GrSum_isGradedMap_map
-- name    : GlobalTheory.GrSum.isGradedMap_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:46.074469+00:00
-- url     : https://prove2.me/theorems/3176e26f-9950-4db9-bc47-3a8780423700
-- title:
--   Gr Sum: is Graded Map map
-- statement:
--   The Gr Sum construction uses the is Graded Map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L673-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L673-L675

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
  {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  {B : ℤ → Type*} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
open GlobalTheory.GrSum
variable {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
  {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)
variable {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]

theorem GlobalTheory.GrSum.isGradedMap_map (φ : ∀ n, A n →ₗ[R] B n) (hφ) :
    IsGradedMap (grading hx) (grading hy) (map hx hy φ hφ) := by sorry
