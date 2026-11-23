-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
-- name    : GlobalTheory.IsSymplecticBasis.left_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:49.700346+00:00
-- url     : https://prove2.me/theorems/64196465-51dd-45ac-a9aa-f7f435606960
-- title:
--   Is Symplectic Basis: left left
-- statement:
--   The Is Symplectic Basis construction uses the left left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L343-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L343-L344

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

theorem GlobalTheory.IsSymplecticBasis.left_left (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inl i)) (b (Sum.inl j)) = 0 := by sorry
