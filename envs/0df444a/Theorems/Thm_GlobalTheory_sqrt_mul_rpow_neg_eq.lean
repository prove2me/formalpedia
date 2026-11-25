-- Prove2me | Theorems.Thm_GlobalTheory_sqrt_mul_rpow_neg_eq
-- name    : GlobalTheory.sqrt_mul_rpow_neg_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:55:18.53087+00:00
-- url     : https://prove2.me/theorems/75e0cc22-601a-59b1-b2e3-9475b2ef0337
-- title:
--   Global Theory: sqrt mul rpow neg eq
-- statement:
--   The Global Theory construction uses the sqrt mul rpow neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiveElementaryInequalitiesEventually.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiveElementaryInequalitiesEventually.lean#L16-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiveElementaryInequalitiesEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Real
open GlobalTheory

theorem GlobalTheory.sqrt_mul_rpow_neg_eq (eps x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * x ^ (-(eps / 8))) = x ^ (1 / 2 - eps / 16) := by sorry
