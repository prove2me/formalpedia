-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticFamily_linearIndependent
-- name    : GlobalTheory.IsSymplecticFamily.linearIndependent
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:59.891201+00:00
-- url     : https://prove2.me/theorems/fe17343f-e9d3-44e3-bbf5-f9e3543faae1
-- title:
--   Is Symplectic Family: linear Independent
-- statement:
--   The Is Symplectic Family construction uses the linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L85-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L85-L98

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

theorem GlobalTheory.IsSymplecticFamily.linearIndependent [Finite ι] [IsDomain R] (h : IsSymplecticFamily B e f d)
    (hd : ∀ i, d i ≠ 0) : LinearIndependent R (Sum.elim e f) := by sorry
