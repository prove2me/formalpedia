-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Counting_card_comap_eq_card_ker_mul_card_range_inf
-- name    : GlobalTheory.CompanionTheory.Counting.card_comap_eq_card_ker_mul_card_range_inf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:48.164802+00:00
-- url     : https://prove2.me/theorems/827866d7-9390-419b-9316-96c333ab4717
-- title:
--   Counting: card comap eq card ker mul card range inf
-- statement:
--   The Counting construction uses the card comap eq card ker mul card range inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardComapEqCardKerMulCardRangeInf.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardComapEqCardKerMulCardRangeInf.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardComapEqCardKerMulCardRangeInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Counting

theorem GlobalTheory.CompanionTheory.Counting.card_comap_eq_card_ker_mul_card_range_inf :
    ∀ (R A X : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A] [AddCommGroup X]
      [Module R X] (f : A →ₗ[R] X) (U : Submodule R X),
      Nat.card ↥(U.comap f) = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f ⊓ U) := by sorry
