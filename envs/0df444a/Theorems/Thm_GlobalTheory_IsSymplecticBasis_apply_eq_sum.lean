-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_eq_sum
-- name    : GlobalTheory.IsSymplecticBasis.apply_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:54.478936+00:00
-- url     : https://prove2.me/theorems/0b9d44ae-fe5c-44db-a783-ed76df4f74be
-- title:
--   Is Symplectic Basis: apply eq sum
-- statement:
--   The Is Symplectic Basis construction uses the apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L365-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L365-L368

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
open GlobalTheory.IsSymplecticBasis
variable {b : Basis (ι ⊕ ι) R M}

theorem GlobalTheory.IsSymplecticBasis.apply_eq_sum [Fintype ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) (x y : M) :
    B x y = ∑ i, (b.repr x (Sum.inl i) * b.repr y (Sum.inr i) -
      b.repr x (Sum.inr i) * b.repr y (Sum.inl i)) := by sorry
