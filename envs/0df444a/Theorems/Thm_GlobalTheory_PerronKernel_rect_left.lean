-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_rect_left
-- name    : GlobalTheory.PerronKernel.rect_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:41.447566+00:00
-- url     : https://prove2.me/theorems/c999cf30-4918-4613-906b-79f304093512
-- title:
--   Perron Kernel: rect left
-- statement:
--   The Perron Kernel construction uses the rect left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L141-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L141-L206

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

theorem GlobalTheory.PerronKernel.rect_left (L : ℝ) {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (∫ x in a..b, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    - (∫ x in a..b, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    + I * (∫ t in (-T)..T, cexp (L * ((b : ℂ) + t * I)) / ((b : ℂ) + t * I))
    - I * (∫ t in (-T)..T, cexp (L * ((a : ℂ) + t * I)) / ((a : ℂ) + t * I))
      = 2 * Real.pi * I := by sorry
