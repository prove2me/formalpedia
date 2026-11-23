-- Prove2me | Theorems.Thm_GlobalTheory_not_summable_two_add_two_re_pow_div
-- name    : GlobalTheory.not_summable_two_add_two_re_pow_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:44.433112+00:00
-- url     : https://prove2.me/theorems/77bbcd44-d2b8-476c-af8f-49b2225f51fc
-- title:
--   Global Theory: not summable two add two re pow div
-- statement:
--   The Global Theory construction uses the not summable two add two re pow div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EulerProductNeZeroOneOfEntire.lean#L20-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EulerProductNeZeroOneOfEntire.lean#L20-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
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
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem GlobalTheory.not_summable_two_add_two_re_pow_div (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ¬ Summable fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) := by sorry
