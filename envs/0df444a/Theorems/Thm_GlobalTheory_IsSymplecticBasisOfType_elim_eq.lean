-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_elim_eq
-- name    : GlobalTheory.IsSymplecticBasisOfType.elim_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:58.027857+00:00
-- url     : https://prove2.me/theorems/7b424ab6-156c-4af1-a6a5-b878ddd5fe9b
-- title:
--   Is Symplectic Basis Of Type: elim eq
-- statement:
--   The Is Symplectic Basis Of Type construction uses the elim eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L273-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L273-L275

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

theorem GlobalTheory.IsSymplecticBasisOfType.elim_eq (b : Basis (ι ⊕ ι) R M) :
    Sum.elim (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) = b := by sorry
