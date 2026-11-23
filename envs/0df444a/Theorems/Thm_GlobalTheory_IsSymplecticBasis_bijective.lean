-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_bijective
-- name    : GlobalTheory.IsSymplecticBasis.bijective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:08.688892+00:00
-- url     : https://prove2.me/theorems/443ddf07-16d9-4ecd-8f3a-1e9364cf5efa
-- title:
--   Is Symplectic Basis: bijective
-- statement:
--   The Is Symplectic Basis construction uses the bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L383-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L383-L398

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

theorem GlobalTheory.IsSymplecticBasis.bijective [Finite ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) : Bijective B := by sorry
