-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosed_fixedSubalgebra
-- name    : GlobalTheory.isIntegrallyClosed_fixedSubalgebra
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:54.433798+00:00
-- url     : https://prove2.me/theorems/98d60f3b-0406-52a6-9e7a-dd13a7099513
-- title:
--   Global Theory: is Integrally Closed fixed Subalgebra
-- statement:
--   The Global Theory construction uses the is Integrally Closed fixed Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L73-L76

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

theorem GlobalTheory.isIntegrallyClosed_fixedSubalgebra (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [IsDomain A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed (FixedPoints.subalgebra R A G) := by sorry
