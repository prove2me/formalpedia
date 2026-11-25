-- Prove2me | Theorems.Thm_GlobalTheory_iInf_primeLocalSubalgebra_height_eq_one
-- name    : GlobalTheory.iInf_primeLocalSubalgebra_height_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:00.886989+00:00
-- url     : https://prove2.me/theorems/3a33793c-8a0b-479a-bb82-dbdbf2d24c6a
-- title:
--   Global Theory: i Inf prime Local Subalgebra height eq one
-- statement:
--   The Global Theory construction uses the i Inf prime Local Subalgebra height eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L494-L498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L494-L498

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
variable (A K)

theorem GlobalTheory.iInf_primeLocalSubalgebra_height_eq_one :
    ⨅ p : {p : PrimeSpectrum A // p.asIdeal.height = 1}, primeLocalSubalgebra K p.1.asIdeal = ⊥ := by sorry
