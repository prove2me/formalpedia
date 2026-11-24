-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_near
-- name    : GlobalTheory.PerronKernel.near
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:18.522024+00:00
-- url     : https://prove2.me/theorems/162a3e0c-be6e-4b1c-a8a0-e46481bff70d
-- title:
--   Perron Kernel: near
-- statement:
--   The Perron Kernel construction uses the near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L291-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L291-L344

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

theorem GlobalTheory.PerronKernel.near (L : ℝ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)‖
      ≤ Real.exp (L * c) * (Real.pi + 2 * (T * |L|)) := by sorry
