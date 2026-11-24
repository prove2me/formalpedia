-- Prove2me | Theorems.Thm_GlobalTheory_one_sub_re_pos_of_norm_le_half
-- name    : GlobalTheory.one_sub_re_pos_of_norm_le_half
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:20.833615+00:00
-- url     : https://prove2.me/theorems/198c5de5-7056-48f3-8f6c-9e692dfe710d
-- title:
--   Global Theory: one sub re pos of norm le half
-- statement:
--   The Global Theory construction uses the one sub re pos of norm le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/OneSubRePosOfNormLeHalf.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/OneSubRePosOfNormLeHalf.lean#L25-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_OneSubRePosOfNormLeHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.one_sub_re_pos_of_norm_le_half (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : 0 < (1 - z).re := by sorry
