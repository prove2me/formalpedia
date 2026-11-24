-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_hinv
-- name    : GlobalTheory.PerronKernel.hinv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:22.846396+00:00
-- url     : https://prove2.me/theorems/a2a521b1-d009-4de7-9aac-08d92e1e0ef0
-- title:
--   Perron Kernel: hinv
-- statement:
--   The Perron Kernel construction uses the hinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L63-L73

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

theorem GlobalTheory.PerronKernel.hinv {T : ℝ} (h : T ≠ 0) (a b : ℝ) :
    (∫ x in a..b, ((x : ℂ) + ((-T : ℝ) : ℂ) * I)⁻¹) - ∫ x in a..b, ((x : ℂ) + T * I)⁻¹
      = 2 * I * ((Real.arctan (b / T) - Real.arctan (a / T) : ℝ) : ℂ) := by sorry
