-- Prove2me | Theorems.Thm_GlobalTheory_conj_neg_log_euler_factor
-- name    : GlobalTheory.conj_neg_log_euler_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:55.456156+00:00
-- url     : https://prove2.me/theorems/1b0590e1-807a-41c0-83fb-83fdcf4e7849
-- title:
--   Global Theory: conj neg log euler factor
-- statement:
--   The Global Theory construction uses the conj neg log euler factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EulerProductNeZeroOneOfEntire.lean#L73-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EulerProductNeZeroOneOfEntire.lean#L73-L90

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

theorem GlobalTheory.conj_neg_log_euler_factor (n : ℕ) (hn : 2 ≤ n) (c : ℂ) (hc : ‖c‖ ≤ 1) (s : ℂ)
    (hs : 1 < s.re) :
    starRingEnd ℂ (-Complex.log (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s)))) =
      -Complex.log (1 - starRingEnd ℂ c * (n : ℂ) ^ (-s)) := by sorry
