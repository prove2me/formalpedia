-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_two_zmod_pow
-- name    : GlobalTheory.isUnit_two_zmod_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:28.422458+00:00
-- url     : https://prove2.me/theorems/1f4276d7-b496-4e47-9745-83f97ddc82ff
-- title:
--   Global Theory: is Unit two zmod pow
-- statement:
--   The Global Theory construction uses the is Unit two zmod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L63-L65

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

theorem GlobalTheory.isUnit_two_zmod_pow (hn : Odd n) (k : ℕ) : IsUnit (2 : ZMod (n ^ k)) := by sorry
