-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_summable_sg
-- name    : GlobalTheory.PhiGam.summable_sg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:28.267983+00:00
-- url     : https://prove2.me/theorems/93df91d8-0176-4489-9566-bea4516d22c4
-- title:
--   Phi Gam: summable sg
-- statement:
--   The Phi Gam construction uses the summable sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L189-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L189-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem GlobalTheory.PhiGam.summable_sg {l n : ℕ} [NeZero n] (hl : 2 ≤ l) (h : ZMod n → ℕ) (i : ZMod n) :
    Summable fun j : ℕ => (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by sorry
