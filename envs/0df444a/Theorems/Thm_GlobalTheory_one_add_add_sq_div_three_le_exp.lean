-- Prove2me | Theorems.Thm_GlobalTheory_one_add_add_sq_div_three_le_exp
-- name    : GlobalTheory.one_add_add_sq_div_three_le_exp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:15.503948+00:00
-- url     : https://prove2.me/theorems/f13e9113-1918-4a31-abdd-4fa52ead2173
-- title:
--   Global Theory: one add add sq div three le exp
-- statement:
--   The Global Theory construction uses the one add add sq div three le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExpQuadraticLowerAndLogLinearLower.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExpQuadraticLowerAndLogLinearLower.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory

theorem GlobalTheory.one_add_add_sq_div_three_le_exp (u : ℝ) (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by sorry
