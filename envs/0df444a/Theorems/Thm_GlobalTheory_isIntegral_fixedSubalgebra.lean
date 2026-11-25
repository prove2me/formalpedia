-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_fixedSubalgebra
-- name    : GlobalTheory.isIntegral_fixedSubalgebra
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:05.256468+00:00
-- url     : https://prove2.me/theorems/312f3900-b069-41ba-adc8-72db3216d1ec
-- title:
--   Global Theory: is Integral fixed Subalgebra
-- statement:
--   The Global Theory construction uses the is Integral fixed Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L28-L30

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

theorem GlobalTheory.isIntegral_fixedSubalgebra [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] : Algebra.IsIntegral (FixedPoints.subalgebra R A G) A := by sorry
