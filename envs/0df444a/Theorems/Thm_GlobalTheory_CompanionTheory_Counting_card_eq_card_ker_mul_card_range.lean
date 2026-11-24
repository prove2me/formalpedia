-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Counting_card_eq_card_ker_mul_card_range
-- name    : GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:46.924794+00:00
-- url     : https://prove2.me/theorems/cdef3016-1b96-4cae-906a-a87261cd85a4
-- title:
--   Counting: card eq card ker mul card range
-- statement:
--   The Counting construction uses the card eq card ker mul card range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardEqCardKerMulCardRange.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardEqCardKerMulCardRange.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardEqCardKerMulCardRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Counting

theorem GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range (R A B : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) :
    Nat.card A = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f) := by sorry
