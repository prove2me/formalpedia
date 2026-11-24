-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_swap
-- name    : GlobalTheory.IsSymplecticBasis.swap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:58.942577+00:00
-- url     : https://prove2.me/theorems/9fb143a6-0c59-4252-8c10-323deeddfb45
-- title:
--   Is Symplectic Basis: swap
-- statement:
--   The Is Symplectic Basis construction uses the swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L375-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L375-L377

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

theorem GlobalTheory.IsSymplecticBasis.swap (h : IsSymplecticBasis B b) (hB : B.IsAlt) :
    IsSymplecticBasis (-B) (b.reindex (Equiv.sumComm ι ι)) := by sorry
