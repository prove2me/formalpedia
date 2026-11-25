-- Prove2me | Theorems.Thm_GlobalTheory_isNoetherianRing_fixedSubalgebra
-- name    : GlobalTheory.isNoetherianRing_fixedSubalgebra
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:27.375796+00:00
-- url     : https://prove2.me/theorems/d8e6c62d-3479-4218-b594-4c2dfbba8e02
-- title:
--   Global Theory: is Noetherian Ring fixed Subalgebra
-- statement:
--   The Global Theory construction uses the is Noetherian Ring fixed Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L103-L107

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

theorem GlobalTheory.isNoetherianRing_fixedSubalgebra [Finite G] (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    IsNoetherianRing (FixedPoints.subalgebra R A G) := by sorry
