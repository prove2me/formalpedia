-- Prove2me | Theorems.Thm_GlobalTheory_heightOneOrd_vw_of_irreducible
-- name    : GlobalTheory.heightOneOrd_vw_of_irreducible
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:58.874885+00:00
-- url     : https://prove2.me/theorems/a5c4380e-f672-462c-802a-b5179b3f27ac
-- title:
--   Global Theory: height One Ord vw of irreducible
-- statement:
--   The Global Theory construction uses the height One Ord vw of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L530-L534
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L530-L534

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
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)

theorem GlobalTheory.heightOneOrd_vw_of_irreducible {ϖ : primeLocalSubalgebra K p} (hϖ : Irreducible ϖ) :
    heightOneOrd_vw p hp (ϖ : K) = 1 := by sorry
