-- Prove2me | Theorems.Thm_GlobalTheory_bilin_eq_zero_of_const_on_cosets
-- name    : GlobalTheory.bilin_eq_zero_of_const_on_cosets
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:36.327012+00:00
-- url     : https://prove2.me/theorems/419b3a58-ef71-4c7f-8cd6-4893e759d17f
-- title:
--   Global Theory: bilin eq zero of const on cosets
-- statement:
--   The Global Theory construction uses the bilin eq zero of const on cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L33-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem GlobalTheory.bilin_eq_zero_of_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) : B = 0 := by sorry
