-- Prove2me | Theorems.Thm_GlobalTheory_exists_ne_zero_mul_mem_of_isIntegral_of_fraction
-- name    : GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:20.586923+00:00
-- url     : https://prove2.me/theorems/44076364-6ad7-585b-88ae-b2e6b065b224
-- title:
--   Global Theory: exists ne zero mul mem of is Integral of fraction
-- statement:
--   The Global Theory construction uses the exists ne zero mul mem of is Integral of fraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConductorNeZeroFiniteTypeCharZero.lean#L12-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConductorNeZeroFiniteTypeCharZero.lean#L12-L45

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

theorem GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction (K R B : Type) [Field K] [CharZero K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [CommRing B] [IsDomain B]
    [Algebra R B] (hinj : Function.Injective (algebraMap R B)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x : B, IsIntegral R x →
      (∃ r s : R, r ≠ 0 ∧ algebraMap R B r * x = algebraMap R B s) →
      ∃ s : R, algebraMap R B c * x = algebraMap R B s := by sorry
