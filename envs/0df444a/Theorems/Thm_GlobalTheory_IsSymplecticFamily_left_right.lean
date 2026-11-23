-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
-- name    : GlobalTheory.IsSymplecticFamily.left_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:56.952004+00:00
-- url     : https://prove2.me/theorems/0b767b91-3f6f-4ead-b049-4eb865256be4
-- title:
--   Is Symplectic Family: left right
-- statement:
--   The Is Symplectic Family construction uses the left right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L56-L60

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

theorem GlobalTheory.IsSymplecticFamily.left_right [DecidableEq ι] (h : IsSymplecticFamily B e f d) (i j : ι) :
    B (e i) (f j) = if i = j then d i else 0 := by sorry
