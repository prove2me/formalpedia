-- Prove2me | Theorems.Thm_GlobalTheory_standardAltForm_apply
-- name    : GlobalTheory.standardAltForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:00.929235+00:00
-- url     : https://prove2.me/theorems/8c9ed195-0470-4137-8920-f19e7352143d
-- title:
--   Global Theory: standard Alt Form apply
-- statement:
--   The Global Theory construction uses the standard Alt Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L28-L37

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

theorem GlobalTheory.standardAltForm_apply [Fintype ι] [DecidableEq ι] (d : ι → R) (x y : ι ⊕ ι → R) :
    standardAltForm d x y =
      ∑ i, d i * (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by sorry
