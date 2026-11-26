-- Prove2me | Theorems.Thm_GlobalTheory_mem_fixedSubalgebra_iff
-- name    : GlobalTheory.mem_fixedSubalgebra_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:24.582566+00:00
-- url     : https://prove2.me/theorems/e227d959-229e-4954-a377-2d5c9442978f
-- title:
--   Global Theory: mem fixed Subalgebra iff
-- statement:
--   The Global Theory construction uses the mem fixed Subalgebra iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L14-L16

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

theorem GlobalTheory.mem_fixedSubalgebra_iff (R : Type*) [CommRing R] [Algebra R A] [SMulCommClass G R A]
    {a : A} : a ∈ FixedPoints.subalgebra R A G ↔ ∀ g : G, g • a = a := by sorry
