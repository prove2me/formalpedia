-- Prove2me | Theorems.Thm_GlobalTheory_SmoothedSumMellin_mellin_sum
-- name    : GlobalTheory.SmoothedSumMellin.mellin_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:18:38.582822+00:00
-- url     : https://prove2.me/theorems/7cec1a47-fb21-4f1d-bada-1608a5f0a0d2
-- title:
--   Smoothed Sum Mellin: mellin sum
-- statement:
--   The Smoothed Sum Mellin construction uses the mellin sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean#L102-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean#L102-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum
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
open Set Filter Asymptotics Topology
open GlobalTheory GlobalTheory.SmoothedSumMellin

theorem GlobalTheory.SmoothedSumMellin.mellin_sum {ι : Type} [Countable ι] {a : ι → ℂ} {N : ι → ℝ} {wt : ℝ → ℂ} {s : ℂ}
    (hw : MellinConvergent wt s) (hN : ∀ i, a i ≠ 0 → 1 ≤ N i)
    (hsum : Summable fun i => ‖a i‖ * N i ^ (-s.re)) :
    mellin (fun t : ℝ => ∑' i, a i * wt (t * N i)) s
      = mellin wt s * ∑' i, a i * (N i : ℂ) ^ (-s) := by sorry
