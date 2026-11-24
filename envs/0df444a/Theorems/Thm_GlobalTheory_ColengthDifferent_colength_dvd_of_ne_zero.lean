-- Prove2me | Theorems.Thm_GlobalTheory_ColengthDifferent_colength_dvd_of_ne_zero
-- name    : GlobalTheory.ColengthDifferent.colength_dvd_of_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:14:29.406801+00:00
-- url     : https://prove2.me/theorems/6dea0fdf-7f66-4ca3-8bbd-b89cfd813833
-- title:
--   Colength Different: colength dvd of ne zero
-- statement:
--   The Colength Different construction uses the colength dvd of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L139-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L139-L225

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
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.ColengthDifferent.colength_dvd_of_ne_zero (F T : Type) [Field F] [CharZero F] [CommRing T] [IsDomain T]
    [Algebra T F] [IsFractionRing T F] (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι → (𝓞 E →+* T))
    (m : ι → ℕ) (g : ℕ) (e : Fin g ≃ Σ i : ι, Fin (m i)) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T)
    (u : ∀ i, Fin (m i) → (Fin g → T)) (hτ : Function.Injective τ)
    (hcard : Fintype.card ι = Module.finrank ℚ E)
    (hsp : ∀ i (w : Fin g → T), (∀ a, (A a).mulVec w = τ i a • w) →
      ∃ cf : Fin (m i) → T, w = ∑ k, cf k • u i k)
    (δ : ι → 𝓞 E) (hδ : ∀ i, δ i ∈ differentIdeal ℤ (𝓞 E)) (hδ0 : ∀ i, δ i ≠ 0) :
    (Matrix.of fun j k : Fin g => u (e j).1 (e j).2 k).det ∣ ∏ i, τ i (δ i) ^ m i := by sorry
