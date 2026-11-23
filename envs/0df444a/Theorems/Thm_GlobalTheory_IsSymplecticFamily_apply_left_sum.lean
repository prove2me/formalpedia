-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticFamily_apply_left_sum
-- name    : GlobalTheory.IsSymplecticFamily.apply_left_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:15.10869+00:00
-- url     : https://prove2.me/theorems/c52dadaf-e825-429c-96e7-1e6a9401754b
-- title:
--   Is Symplectic Family: apply left sum
-- statement:
--   The Is Symplectic Family construction uses the apply left sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L75-L78

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

theorem GlobalTheory.IsSymplecticFamily.apply_left_sum [Fintype ι] (h : IsSymplecticFamily B e f d) (c : ι ⊕ ι → R) (k : ι) :
    B (e k) (∑ i, c i • Sum.elim e f i) = c (Sum.inr k) * d k := by sorry
