-- Prove2me | Theorems.Thm_GlobalTheory_GrSum_of_mem_grading
-- name    : GlobalTheory.GrSum.of_mem_grading
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:20:11.253954+00:00
-- url     : https://prove2.me/theorems/4b3b3061-6dda-4587-a2ae-2465081c8914
-- title:
--   Gr Sum: of mem grading
-- statement:
--   The Gr Sum construction uses the of mem grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L600-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L600-L600

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

theorem GlobalTheory.GrSum.of_mem_grading (n : ℤ) (a : A n) : of hx n a ∈ grading hx n := by sorry
