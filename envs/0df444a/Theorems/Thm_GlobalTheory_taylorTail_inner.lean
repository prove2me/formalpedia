-- Prove2me | Theorems.Thm_GlobalTheory_taylorTail_inner
-- name    : GlobalTheory.taylorTail_inner
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:43.286887+00:00
-- url     : https://prove2.me/theorems/84d39d1a-4550-434f-8a4f-8309997be327
-- title:
--   Global Theory: taylor Tail inner
-- statement:
--   The Global Theory construction uses the taylor Tail inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralTaylorTailIteratedDeriv.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralTaylorTailIteratedDeriv.lean#L26-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.taylorTail_inner (j : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫⁻ t in Ioo (0:ℝ) s, ENNReal.ofReal (t ^ j / (j.factorial : ℝ))
      = ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) := by sorry
