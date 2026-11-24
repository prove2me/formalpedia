-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_isUnit
-- name    : GlobalTheory.IsSymplecticBasisOfType.isUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:57.238394+00:00
-- url     : https://prove2.me/theorems/c9e88be4-0388-4c3b-860b-c0989284f778
-- title:
--   Is Symplectic Basis Of Type: is Unit
-- statement:
--   The Is Symplectic Basis Of Type construction uses the is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L325-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L325-L331

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

theorem GlobalTheory.IsSymplecticBasisOfType.isUnit [Finite ι] (h : IsSymplecticBasisOfType B b d) (hp : Surjective B) (k : ι) :
    IsUnit (d k) := by sorry
