-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_norm_exp_sub_one_ge
-- name    : GlobalTheory.ExpDivision.norm_exp_sub_one_ge
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:07:10.317272+00:00
-- url     : https://prove2.me/theorems/918c6f7b-efc7-45c2-a78c-9cde588e3163
-- title:
--   Exp Division: norm exp sub one ge
-- statement:
--   The Exp Division construction uses the norm exp sub one ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L133-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L133-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision

theorem GlobalTheory.ExpDivision.norm_exp_sub_one_ge (x : ℝ) :
    4 * |x - round x| ≤ ‖Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := by sorry
