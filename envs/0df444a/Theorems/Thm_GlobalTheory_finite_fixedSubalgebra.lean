-- Prove2me | Theorems.Thm_GlobalTheory_finite_fixedSubalgebra
-- name    : GlobalTheory.finite_fixedSubalgebra
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:26.235929+00:00
-- url     : https://prove2.me/theorems/8dc92c03-798d-4f6e-bdd6-e2b6ce4e3b50
-- title:
--   Global Theory: finite fixed Subalgebra
-- statement:
--   The Global Theory construction uses the finite fixed Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L93-L96

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

theorem GlobalTheory.finite_fixedSubalgebra [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [Algebra.FiniteType R A] :
    Module.Finite (FixedPoints.subalgebra R A G) A := by sorry
