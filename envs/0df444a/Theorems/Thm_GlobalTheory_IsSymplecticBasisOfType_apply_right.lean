-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_right
-- name    : GlobalTheory.IsSymplecticBasisOfType.apply_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:47.866858+00:00
-- url     : https://prove2.me/theorems/06e705bd-deb7-45a8-85ea-2117a223db0b
-- title:
--   Is Symplectic Basis Of Type: apply right
-- statement:
--   The Is Symplectic Basis Of Type construction uses the apply right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L283-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L283-L287

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

theorem GlobalTheory.IsSymplecticBasisOfType.apply_right [Finite ι] (h : IsSymplecticBasisOfType B b d) (x : M) (k : ι) :
    B x (b (Sum.inr k)) = b.repr x (Sum.inl k) * d k := by sorry
