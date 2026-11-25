-- Prove2me | Theorems.Thm_GlobalTheory_locPullback_side
-- name    : GlobalTheory.locPullback_side
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:43.272864+00:00
-- url     : https://prove2.me/theorems/4bdb5e6b-1bb3-591f-b0cf-6f0b5dc67ce7
-- title:
--   Global Theory: loc Pullback side
-- statement:
--   The Global Theory construction uses the loc Pullback side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationPreservesRingPullbackSquare.lean#L6-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationPreservesRingPullbackSquare.lean#L6-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMkOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationPreservesRingPullbackSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.locPullback_side {A R LA LR : Type} [CommRing A] [CommRing R] [CommRing LA] [CommRing LR]
    [Algebra A LA] [Algebra R LR] (s : A) [IsLocalization.Away s LA] (φ : A →+* R)
    [IsLocalization.Away (φ s) LR] (Φ : LA →+* LR)
    (hΦ : Φ.comp (algebraMap A LA) = (algebraMap R LR).comp φ)
    (x : LR) (a₀ : A) (r : R) (j k e : ℕ) (he : j + k = e)
    (hx : x * algebraMap R LR (φ s ^ k) = algebraMap R LR r) (ha : φ a₀ = r * φ s ^ j) :
    Φ (IsLocalization.mk' LA a₀ (⟨s ^ e, e, rfl⟩ : Submonoid.powers s)) = x := by sorry
