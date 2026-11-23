-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_isInvariant
-- name    : GlobalTheory.finite_of_isInvariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:58.732384+00:00
-- url     : https://prove2.me/theorems/22210810-3ebb-445e-b09f-05d2db8bac28
-- title:
--   Global Theory: finite of is Invariant
-- statement:
--   The Global Theory construction uses the finite of is Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L78-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]

theorem GlobalTheory.finite_of_isInvariant [Finite G] (R B : Type*) [CommRing R] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [Algebra.IsInvariant B A G]
    [Algebra.FiniteType R A] : Module.Finite B A := by sorry
