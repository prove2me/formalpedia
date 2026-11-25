-- Prove2me | Theorems.Thm_GlobalTheory_SplittingIdempotents_exists_splitting_idempotents_frobenius
-- name    : GlobalTheory.SplittingIdempotents.exists_splitting_idempotents_frobenius
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:39.220102+00:00
-- url     : https://prove2.me/theorems/d96384d2-17c4-419a-b212-b85fb83324f5
-- title:
--   Splitting Idempotents: exists splitting idempotents frobenius
-- statement:
--   The Splitting Idempotents construction uses the exists splitting idempotents frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SplittingIdempotents.lean#L94-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SplittingIdempotents.lean#L94-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SplittingIdempotents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SplittingIdempotents
open GlobalTheory.EigenSplit

theorem GlobalTheory.SplittingIdempotents.exists_splitting_idempotents_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE], ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∃ (m : ℕ) (τ : Fin m ≃ (OE →+* O)) (ε : Fin m → O ⊗[ℤ] OE) (φ : Equiv.Perm (Fin m)), CompleteOrthogonalIdempotents ε ∧ (∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = τ i a • ε i) ∧ (∀ i j, i ≠ j → ∃ a, IsUnit (τ i a - τ j a)) ∧ ∀ i a, τ (φ i) a - τ i a ^ p ∈ IsLocalRing.maximalIdeal O := by sorry
