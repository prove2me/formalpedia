-- Prove2me | Theorems.Thm_GlobalTheory_finiteType_fixedSubalgebra
-- name    : GlobalTheory.finiteType_fixedSubalgebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:49.674426+00:00
-- url     : https://prove2.me/theorems/4780e25d-7af2-4d06-8e65-ee23a903975e
-- title:
--   Global Theory: finite Type fixed Subalgebra
-- statement:
--   The Global Theory construction uses the finite Type fixed Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L98-L101

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

theorem GlobalTheory.finiteType_fixedSubalgebra [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FiniteType R (FixedPoints.subalgebra R A G) := by sorry
