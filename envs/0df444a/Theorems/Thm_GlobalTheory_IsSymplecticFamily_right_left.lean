-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left
-- name    : GlobalTheory.IsSymplecticFamily.right_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:54.38687+00:00
-- url     : https://prove2.me/theorems/34618d90-1931-49a7-99e9-f470bd27902d
-- title:
--   Is Symplectic Family: right left
-- statement:
--   The Is Symplectic Family construction uses the right left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L62-L67

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
open GlobalTheory.IsSymplecticFamily
variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}

theorem GlobalTheory.IsSymplecticFamily.right_left [DecidableEq ι] (h : IsSymplecticFamily B e f d) (hB : B.IsAlt) (i j : ι) :
    B (f i) (e j) = if i = j then -d i else 0 := by sorry
