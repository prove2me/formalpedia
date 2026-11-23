-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_right
-- name    : GlobalTheory.IsSymplecticBasis.apply_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:52.858908+00:00
-- url     : https://prove2.me/theorems/3292925d-48f9-44ba-956b-7b7d9a7fa82f
-- title:
--   Is Symplectic Basis: apply right
-- statement:
--   The Is Symplectic Basis construction uses the apply right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L361-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L361-L363

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

theorem GlobalTheory.IsSymplecticBasis.apply_right [Finite ι] (h : IsSymplecticBasis B b) (x : M) (k : ι) :
    B x (b (Sum.inr k)) = b.repr x (Sum.inl k) := by sorry
