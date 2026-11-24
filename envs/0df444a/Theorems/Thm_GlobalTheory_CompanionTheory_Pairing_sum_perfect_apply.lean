-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Pairing_sum_perfect_apply
-- name    : GlobalTheory.CompanionTheory.Pairing.sum_perfect_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:46.085394+00:00
-- url     : https://prove2.me/theorems/fbd76a1c-25bf-4759-b299-c1ffe9552f3d
-- title:
--   Pairing: sum perfect apply
-- statement:
--   The Pairing construction uses the sum perfect apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SumPerfectApply.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SumPerfectApply.lean#L5-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumPerfectApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Pairing

theorem GlobalTheory.CompanionTheory.Pairing.sum_perfect_apply {R : Type} [CommRing R] {ι : Type} [Fintype ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] [∀ i, AddCommGroup (Y i)]
    [∀ i, Module R (Y i)] (B : ∀ i, Y i →ₗ[R] X i →ₗ[R] R)
    (y : ∀ i, Y i) (x : ∀ i, X i) :
    (∑ i, (B i).compl₁₂ (LinearMap.proj i : (∀ i, Y i) →ₗ[R] Y i)
      (LinearMap.proj i : (∀ i, X i) →ₗ[R] X i)) y x = ∑ i, B i (y i) (x i) := by sorry
