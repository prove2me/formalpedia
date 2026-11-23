-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_nsmul_of_nsmul_eq_zero_zmod
-- name    : GlobalTheory.exists_eq_nsmul_of_nsmul_eq_zero_zmod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:06.623977+00:00
-- url     : https://prove2.me/theorems/a8673a85-579f-4bb6-99c0-269ff39cd2f3
-- title:
--   Global Theory: exists eq nsmul of nsmul eq zero zmod
-- statement:
--   The Global Theory construction uses the exists eq nsmul of nsmul eq zero zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L70-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L70-L80

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
variable {n k : ℕ}

theorem GlobalTheory.exists_eq_nsmul_of_nsmul_eq_zero_zmod (hn : n ≠ 0) (hk : 2 ≤ k) (x : ZMod (n ^ k))
    (hx : n • x = 0) : ∃ a, x = n • a := by sorry
