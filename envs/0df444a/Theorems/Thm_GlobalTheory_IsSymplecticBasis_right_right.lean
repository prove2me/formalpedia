-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
-- name    : GlobalTheory.IsSymplecticBasis.right_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:58.49434+00:00
-- url     : https://prove2.me/theorems/5cf85ff7-a5cd-4db3-a14e-ac280b7a8f63
-- title:
--   Is Symplectic Basis: right right
-- statement:
--   The Is Symplectic Basis construction uses the right right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L346-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L346-L347

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

theorem GlobalTheory.IsSymplecticBasis.right_right (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inr i)) (b (Sum.inr j)) = 0 := by sorry
