-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_norm_iteratedDeriv_rem_le
-- name    : GlobalTheory.CharFormDeriv.norm_iteratedDeriv_rem_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:21.067983+00:00
-- url     : https://prove2.me/theorems/ffbef8a6-b76e-483e-b7a3-77c946d35f50
-- title:
--   Char Form Deriv: norm iterated Deriv rem le
-- statement:
--   The Char Form Deriv construction uses the norm iterated Deriv rem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L74-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L74-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv

theorem GlobalTheory.CharFormDeriv.norm_iteratedDeriv_rem_le {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) (i : ℕ) (y : ℝ) :
    ‖iteratedDeriv i (rem t) y‖ ≤ 3 * |t| * (1 + |y|) ^ 2 := by sorry
