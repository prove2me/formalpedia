-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_exp_pi_I_int
-- name    : GlobalTheory.OfPeriod.exp_pi_I_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:20.490818+00:00
-- url     : https://prove2.me/theorems/b371eee2-a7da-4b41-9058-146920e45476
-- title:
--   Of Period: exp pi I int
-- statement:
--   The Of Period construction uses the exp pi I int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpPiIInt.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpPiIInt.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpPiIInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Complex

theorem GlobalTheory.OfPeriod.exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * I * ((n : ℝ) : ℂ)) = (-1) ^ n := by sorry
