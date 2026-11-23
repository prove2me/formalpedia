-- Prove2me | Theorems.Thm_GlobalTheory_one_add_two_mul_div_pow_le
-- name    : GlobalTheory.one_add_two_mul_div_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:31.351411+00:00
-- url     : https://prove2.me/theorems/52138051-83d6-4689-aaa9-62473f9e550a
-- title:
--   Global Theory: one add two mul div pow le
-- statement:
--   The Global Theory construction uses the one add two mul div pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteInterClosedBallOfSeparated.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteInterClosedBallOfSeparated.lean#L42-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.one_add_two_mul_div_pow_le {d R : ℝ} (hd : 0 < d) (hR : d ≤ R) (n : ℕ) :
    (1 + 2 * R / d) ^ n ≤ (3 * R / d) ^ n := by sorry
