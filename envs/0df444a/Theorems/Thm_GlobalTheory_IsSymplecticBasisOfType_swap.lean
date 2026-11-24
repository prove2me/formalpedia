-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_swap
-- name    : GlobalTheory.IsSymplecticBasisOfType.swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:53.742231+00:00
-- url     : https://prove2.me/theorems/eb6f45ca-dc3d-435a-9d32-8a2f94ed1c63
-- title:
--   Is Symplectic Basis Of Type: swap
-- statement:
--   The Is Symplectic Basis Of Type construction uses the swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L313-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L313-L315

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

theorem GlobalTheory.IsSymplecticBasisOfType.swap (h : IsSymplecticBasisOfType B b d) (hB : B.IsAlt) :
    IsSymplecticBasisOfType (-B) (b.reindex (Equiv.sumComm ι ι)) d := by sorry
