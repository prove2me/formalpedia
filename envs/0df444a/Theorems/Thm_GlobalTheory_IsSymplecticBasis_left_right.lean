-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
-- name    : GlobalTheory.IsSymplecticBasis.left_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:52.05946+00:00
-- url     : https://prove2.me/theorems/0300a609-d265-4893-8e4e-bfa45abdd9af
-- title:
--   Is Symplectic Basis: left right
-- statement:
--   The Is Symplectic Basis construction uses the left right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L349-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L349-L351

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

theorem GlobalTheory.IsSymplecticBasis.left_right [DecidableEq ι] (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0 := by sorry
