-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticFamily_swap
-- name    : GlobalTheory.IsSymplecticFamily.swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:15.226543+00:00
-- url     : https://prove2.me/theorems/9096d087-4fd7-499d-b325-73718a747270
-- title:
--   Is Symplectic Family: swap
-- statement:
--   The Is Symplectic Family construction uses the swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L69-L73

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

theorem GlobalTheory.IsSymplecticFamily.swap (h : IsSymplecticFamily B e f d) (hB : B.IsAlt) : IsSymplecticFamily (-B) f e d := by sorry
