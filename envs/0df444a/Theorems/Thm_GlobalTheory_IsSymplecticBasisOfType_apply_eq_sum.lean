-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum
-- name    : GlobalTheory.IsSymplecticBasisOfType.apply_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:50.261244+00:00
-- url     : https://prove2.me/theorems/4cef0d5f-839d-4ed2-bcd5-56b8c9aac0e0
-- title:
--   Is Symplectic Basis Of Type: apply eq sum
-- statement:
--   The Is Symplectic Basis Of Type construction uses the apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L289-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L289-L297

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
  {B : LinearMap.BilinForm R M}
open GlobalTheory.IsSymplecticBasisOfType
variable {b : Basis (ι ⊕ ι) R M} {d : ι → R}

theorem GlobalTheory.IsSymplecticBasisOfType.apply_eq_sum [Fintype ι] (h : IsSymplecticBasisOfType B b d) (hB : B.IsAlt) (x y : M) :
    B x y = ∑ i, d i * (b.repr x (Sum.inl i) * b.repr y (Sum.inr i) -
      b.repr x (Sum.inr i) * b.repr y (Sum.inl i)) := by sorry
