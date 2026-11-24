-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticFamily_sum
-- name    : GlobalTheory.IsSymplecticFamily.sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:21:09.564966+00:00
-- url     : https://prove2.me/theorems/580fc768-1eea-4857-8fe2-229440c802a9
-- title:
--   Is Symplectic Family: sum
-- statement:
--   The Is Symplectic Family construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L100-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L100-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.IsSymplecticFamily
variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}

theorem GlobalTheory.IsSymplecticFamily.sum {κ : Type*} {e' f' : κ → M} {d' : κ → R} (hB : B.IsAlt)
    (h : IsSymplecticFamily B e f d) (h' : IsSymplecticFamily B e' f' d')
    (h₁ : ∀ i j, B (e i) (e' j) = 0) (h₂ : ∀ i j, B (e i) (f' j) = 0)
    (h₃ : ∀ i j, B (f i) (e' j) = 0) (h₄ : ∀ i j, B (f i) (f' j) = 0) :
    IsSymplecticFamily B (Sum.elim e e') (Sum.elim f f') (Sum.elim d d') := by sorry
