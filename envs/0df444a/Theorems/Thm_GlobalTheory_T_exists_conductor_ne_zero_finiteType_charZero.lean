-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_conductor_ne_zero_finiteType_charZero
-- name    : GlobalTheory.T.exists_conductor_ne_zero_finiteType_charZero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:16:25.304813+00:00
-- url     : https://prove2.me/theorems/9f9287d4-0504-447f-bb8f-c82ee602e10a
-- title:
--   T: exists conductor ne zero finite Type char Zero
-- statement:
--   The T construction uses the exists conductor ne zero finite Type char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConductorNeZeroFiniteTypeCharZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConductorNeZeroFiniteTypeCharZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConductorNeZeroFiniteTypeCharZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConductorNeZeroFiniteTypeCharZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_conductor_ne_zero_finiteType_charZero : ∀ (K R B : Type) [Field K] [CharZero K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [CommRing B] [IsDomain B] [Algebra R B], Function.Injective (algebraMap R B) → ∃ c : R, c ≠ 0 ∧ ∀ x : B, IsIntegral R x → (∃ r s : R, r ≠ 0 ∧ algebraMap R B r * x = algebraMap R B s) → ∃ s : R, algebraMap R B c * x = algebraMap R B s := by sorry
