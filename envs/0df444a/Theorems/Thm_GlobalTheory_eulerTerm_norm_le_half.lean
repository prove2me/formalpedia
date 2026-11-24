-- Prove2me | Theorems.Thm_GlobalTheory_eulerTerm_norm_le_half
-- name    : GlobalTheory.eulerTerm_norm_le_half
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:19:50.23764+00:00
-- url     : https://prove2.me/theorems/5e1fc281-0ed3-42f0-b445-3066f0ecc9fc
-- title:
--   Global Theory: euler Term norm le half
-- statement:
--   The Global Theory construction uses the euler Term norm le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/OneSubRePosOfNormLeHalf.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/OneSubRePosOfNormLeHalf.lean#L16-L23

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

theorem GlobalTheory.eulerTerm_norm_le_half (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 1 < s.re) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ 1 / 2 := by sorry
