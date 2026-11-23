-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_toMatrix_eq
-- name    : GlobalTheory.IsSymplecticBasis.toMatrix_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:56.31307+00:00
-- url     : https://prove2.me/theorems/1c36ccb0-f94e-4979-9853-9d6f704d6fc5
-- title:
--   Is Symplectic Basis: to Matrix eq
-- statement:
--   The Is Symplectic Basis construction uses the to Matrix eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L370-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L370-L373

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

theorem GlobalTheory.IsSymplecticBasis.toMatrix_eq [Fintype ι] [DecidableEq ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) :
    LinearMap.BilinForm.toMatrix b B = -Matrix.J ι R := by sorry
