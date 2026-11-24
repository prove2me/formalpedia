-- Prove2me | Theorems.Thm_GlobalTheory_finite_height_eq_one_mem
-- name    : GlobalTheory.finite_height_eq_one_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:15.426357+00:00
-- url     : https://prove2.me/theorems/2ccb9624-969f-4af5-babc-3bcba83399bf
-- title:
--   Global Theory: finite height eq one mem
-- statement:
--   The Global Theory construction uses the finite height eq one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L23-L28

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
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

theorem GlobalTheory.finite_height_eq_one_mem {a : A} (ha : a ≠ 0) :
    {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite := by sorry
