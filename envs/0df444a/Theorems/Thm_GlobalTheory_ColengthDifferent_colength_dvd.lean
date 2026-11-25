-- Prove2me | Theorems.Thm_GlobalTheory_ColengthDifferent_colength_dvd
-- name    : GlobalTheory.ColengthDifferent.colength_dvd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:06.66628+00:00
-- url     : https://prove2.me/theorems/791792b4-bc6e-47b6-b032-80ffb87676c0
-- title:
--   Colength Different: colength dvd
-- statement:
--   The Colength Different construction uses the colength dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L229-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L229-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent

theorem GlobalTheory.ColengthDifferent.colength_dvd : ∀ (E F T : Type) [Field E] [NumberField E] [Field F] [CharZero F] [CommRing T] [IsDomain T] [Algebra T F] [IsFractionRing T F] (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι → (𝓞 E →+* T)) (m : ι → ℕ) (g : ℕ) (e : Fin g ≃ Σ i : ι, Fin (m i)) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T) (u : ∀ i, Fin (m i) → (Fin g → T)), Function.Injective τ → Fintype.card ι = Module.finrank ℚ E → IsIntegrallyClosed T → (∀ i (w : Fin g → T), (∀ a, (A a).mulVec w = τ i a • w) → ∃ cf : Fin (m i) → T, w = ∑ k, cf k • u i k) → (∀ i k a, (A a).mulVec (u i k) = τ i a • u i k) → ∀ δ : ι → 𝓞 E, (∀ i, δ i ∈ differentIdeal ℤ (𝓞 E)) → (Matrix.of fun j k : Fin g => u (e j).1 (e j).2 k).det ∣ ∏ i, τ i (δ i) ^ m i := by sorry
