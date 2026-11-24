-- Prove2me | Theorems.Thm_GlobalTheory_meets_cosets_nsmul_of_meets_cosets_torsion
-- name    : GlobalTheory.meets_cosets_nsmul_of_meets_cosets_torsion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:44.764826+00:00
-- url     : https://prove2.me/theorems/0a06b56b-94e3-4ab0-be32-52d386436daf
-- title:
--   Global Theory: meets cosets nsmul of meets cosets torsion
-- statement:
--   The Global Theory construction uses the meets cosets nsmul of meets cosets torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L82-L88

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

theorem GlobalTheory.meets_cosets_nsmul_of_meets_cosets_torsion {ι : Type*} (hn : n ≠ 0) (hk : 2 ≤ k)
    (T : Set (ι → ZMod (n ^ k))) (hT : ∀ x, ∃ t ∈ T, n • (x - t) = 0) (x : ι → ZMod (n ^ k)) :
    ∃ t ∈ T, ∃ a, x = t + n • a := by sorry
