-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_sum_char_dot_eq_zero
-- name    : GlobalTheory.GramCount.sum_char_dot_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:14.675333+00:00
-- url     : https://prove2.me/theorems/25d3da30-0abe-56b4-a21a-d275e9ad7cac
-- title:
--   Gram Count: sum char dot eq zero
-- statement:
--   The Gram Count construction uses the sum char dot eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrimitiveTupleOfLinearIndependentFiniteRing.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrimitiveTupleOfLinearIndependentFiniteRing.lean#L9-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrimitiveTupleOfLinearIndependentFiniteRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount

theorem GlobalTheory.GramCount.sum_char_dot_eq_zero {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {m : ℕ} (t : Fin m → B) (ht : t ≠ 0) :
    ∑ s : Fin m → B, χ (∑ a, s a * t a) = 0 := by sorry
