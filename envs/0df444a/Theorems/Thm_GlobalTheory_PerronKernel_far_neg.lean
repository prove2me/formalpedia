-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_far_neg
-- name    : GlobalTheory.PerronKernel.far_neg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:43:42.846833+00:00
-- url     : https://prove2.me/theorems/f272de71-1939-4780-bad2-b074d5b75d01
-- title:
--   Perron Kernel: far neg
-- statement:
--   The Perron Kernel construction uses the far neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L228-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L228-L257

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel

theorem GlobalTheory.PerronKernel.far_neg {L c T : ℝ} (hL : L < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)‖
      ≤ 2 * Real.exp (L * c) / (T * |L|) := by sorry
