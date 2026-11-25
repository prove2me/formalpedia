-- Prove2me | Theorems.Thm_GlobalTheory_exists_common_denominator_of_fg
-- name    : GlobalTheory.exists_common_denominator_of_fg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:13.621641+00:00
-- url     : https://prove2.me/theorems/71531602-49a2-5e53-8498-37173c3d1f97
-- title:
--   Global Theory: exists common denominator of fg
-- statement:
--   The Global Theory construction uses the exists common denominator of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConductorNeZeroFiniteTypeCharZero.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConductorNeZeroFiniteTypeCharZero.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConductorNeZeroFiniteTypeCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_common_denominator_of_fg {R L : Type*} [CommRing R] [IsDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (N : Submodule R L) (hN : N.FG) :
    ∃ c : R, c ≠ 0 ∧ ∀ y ∈ N, ∃ s : R, algebraMap R L s = c • y := by sorry
