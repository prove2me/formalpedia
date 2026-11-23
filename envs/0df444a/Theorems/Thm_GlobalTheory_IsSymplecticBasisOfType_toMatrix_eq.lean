-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_toMatrix_eq
-- name    : GlobalTheory.IsSymplecticBasisOfType.toMatrix_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:03.541836+00:00
-- url     : https://prove2.me/theorems/5144f922-761e-4d9c-a24e-5c12997433bc
-- title:
--   Is Symplectic Basis Of Type: to Matrix eq
-- statement:
--   The Is Symplectic Basis Of Type construction uses the to Matrix eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L299-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L299-L311

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

theorem GlobalTheory.IsSymplecticBasisOfType.toMatrix_eq [Fintype ι] [DecidableEq ι] (h : IsSymplecticBasisOfType B b d)
    (hB : B.IsAlt) : LinearMap.BilinForm.toMatrix b B =
      Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0 := by sorry
