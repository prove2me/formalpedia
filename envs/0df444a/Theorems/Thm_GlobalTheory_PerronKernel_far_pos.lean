-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_far_pos
-- name    : GlobalTheory.PerronKernel.far_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:44:15.227204+00:00
-- url     : https://prove2.me/theorems/7136e1b5-aab6-4a67-b8f6-69b7e1049b29
-- title:
--   Perron Kernel: far pos
-- statement:
--   The Perron Kernel construction uses the far pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L259-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L259-L289

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

theorem GlobalTheory.PerronKernel.far_pos {L c T : ℝ} (hL : 0 < L) (hc : 0 < c) (hT : 0 < T) :
    ‖(∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)) - 2 * Real.pi‖
      ≤ 2 * Real.exp (L * c) / (T * |L|) := by sorry
