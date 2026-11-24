-- Prove2me | Theorems.Thm_GlobalTheory_LinPhaseSeminorm_norm_cexp_neg_two_pi_I_mul
-- name    : GlobalTheory.LinPhaseSeminorm.norm_cexp_neg_two_pi_I_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:07:14.496061+00:00
-- url     : https://prove2.me/theorems/7490da21-5268-4e47-9df4-8b6d57aa2b6c
-- title:
--   Lin Phase Seminorm: norm cexp neg two pi I mul
-- statement:
--   The Lin Phase Seminorm construction uses the norm cexp neg two pi I mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormSmulLeftLinearPhaseLe.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormSmulLeftLinearPhaseLe.lean#L26-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open Complex
open GlobalTheory GlobalTheory.LinPhaseSeminorm

theorem GlobalTheory.LinPhaseSeminorm.norm_cexp_neg_two_pi_I_mul (r : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by sorry
