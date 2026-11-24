-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Pairing_sum_perfect
-- name    : GlobalTheory.CompanionTheory.Pairing.sum_perfect
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:31.429146+00:00
-- url     : https://prove2.me/theorems/70cd147b-7abc-44b6-b1f5-79a93f842947
-- title:
--   Pairing: sum perfect
-- statement:
--   The Pairing construction uses the sum perfect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SumPerfectApply.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SumPerfectApply.lean#L13-L36

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

theorem GlobalTheory.CompanionTheory.Pairing.sum_perfect : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (X Y : ι → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)] (B : ∀ i, Y i →ₗ[R] X i →ₗ[R] R), (∀ i, Function.Injective (B i)) → (∀ i, Function.Injective (B i).flip) → Function.Injective (∑ i, (B i).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)) ∧ Function.Injective (∑ i, (B i).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)).flip := by sorry
