-- Prove2me | Theorems.Thm_GlobalTheory_finite_heightOneOrd_vw_ne_zero
-- name    : GlobalTheory.finite_heightOneOrd_vw_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:58.527181+00:00
-- url     : https://prove2.me/theorems/6428b5fb-0808-448b-b347-c257e0cba97d
-- title:
--   Global Theory: finite height One Ord vw ne zero
-- statement:
--   The Global Theory construction uses the finite height One Ord vw ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L454-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L454-L467

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

theorem GlobalTheory.finite_heightOneOrd_vw_ne_zero {x : K} (hx : x ≠ 0) :
    {p : PrimeSpectrum A |
      ∃ hp : p.asIdeal.height = 1, heightOneOrd_vw p.asIdeal hp x ≠ 0}.Finite := by sorry
