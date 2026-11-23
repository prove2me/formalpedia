-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_left
-- name    : GlobalTheory.IsSymplecticBasisOfType.apply_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:53.882548+00:00
-- url     : https://prove2.me/theorems/8a7f51ac-3b20-4e4e-8be1-ab046759cf88
-- title:
--   Is Symplectic Basis Of Type: apply left
-- statement:
--   The Is Symplectic Basis Of Type construction uses the apply left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L277-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L277-L281

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

theorem GlobalTheory.IsSymplecticBasisOfType.apply_left [Finite ι] (h : IsSymplecticBasisOfType B b d) (x : M) (k : ι) :
    B (b (Sum.inl k)) x = b.repr x (Sum.inr k) * d k := by sorry
