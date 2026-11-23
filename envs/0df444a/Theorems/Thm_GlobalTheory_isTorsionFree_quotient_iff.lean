-- Prove2me | Theorems.Thm_GlobalTheory_isTorsionFree_quotient_iff
-- name    : GlobalTheory.isTorsionFree_quotient_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:57.377107+00:00
-- url     : https://prove2.me/theorems/14ca2d7b-0377-49f4-b017-b4643fa5fec7
-- title:
--   Global Theory: is Torsion Free quotient iff
-- statement:
--   The Global Theory construction uses the is Torsion Free quotient iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L503-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L503-L516

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem GlobalTheory.isTorsionFree_quotient_iff [IsDomain R] (I : Submodule R M) :
    IsTorsionFree R (M ⧸ I) ↔ ∀ (r : R) (x : M), r ≠ 0 → r • x ∈ I → x ∈ I := by sorry
