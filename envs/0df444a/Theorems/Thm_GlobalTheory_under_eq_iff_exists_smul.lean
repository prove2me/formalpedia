-- Prove2me | Theorems.Thm_GlobalTheory_under_eq_iff_exists_smul
-- name    : GlobalTheory.under_eq_iff_exists_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:03.612423+00:00
-- url     : https://prove2.me/theorems/865d6446-f452-5405-9012-cededc7e230c
-- title:
--   Global Theory: under eq iff exists smul
-- statement:
--   The Global Theory construction uses the under eq iff exists smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L121-L126

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

theorem GlobalTheory.under_eq_iff_exists_smul [Finite G] (B : Type*) [CommRing B]
    [Algebra B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (Q Q' : Ideal A) [Q.IsPrime] [Q'.IsPrime] :
    Q.under B = Q'.under B ↔ ∃ g : G, Q' = g • Q := by sorry
