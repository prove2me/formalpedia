-- Prove2me | Theorems.Thm_GlobalTheory_isNilpotent_natCast_zmod_pow
-- name    : GlobalTheory.isNilpotent_natCast_zmod_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:19.414943+00:00
-- url     : https://prove2.me/theorems/ee5c6463-7d68-49e7-a497-ed4c610197d5
-- title:
--   Global Theory: is Nilpotent nat Cast zmod pow
-- statement:
--   The Global Theory construction uses the is Nilpotent nat Cast zmod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L67-L68

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

theorem GlobalTheory.isNilpotent_natCast_zmod_pow (n k : ℕ) : IsNilpotent (n : ZMod (n ^ k)) := by sorry
