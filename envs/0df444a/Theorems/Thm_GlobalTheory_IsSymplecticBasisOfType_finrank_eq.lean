-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_finrank_eq
-- name    : GlobalTheory.IsSymplecticBasisOfType.finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:01.096955+00:00
-- url     : https://prove2.me/theorems/4969f01a-4845-4632-bcee-62e9a7e7feb7
-- title:
--   Is Symplectic Basis Of Type: finrank eq
-- statement:
--   The Is Symplectic Basis Of Type construction uses the finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L333-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L333-L335

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

theorem GlobalTheory.IsSymplecticBasisOfType.finrank_eq [Fintype ι] [StrongRankCondition R] (b : Basis (ι ⊕ ι) R M) :
    finrank R M = 2 * Fintype.card ι := by sorry
