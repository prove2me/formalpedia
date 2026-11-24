-- Prove2me | Theorems.Thm_GlobalTheory_SmoothedSumMellin_integral_norm_comp
-- name    : GlobalTheory.SmoothedSumMellin.integral_norm_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:44.900291+00:00
-- url     : https://prove2.me/theorems/4d3b3bae-8b9a-4e28-b9d8-eef122c25cc5
-- title:
--   Smoothed Sum Mellin: integral norm comp
-- statement:
--   The Smoothed Sum Mellin construction uses the integral norm comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean#L76-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean#L76-L100

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

theorem GlobalTheory.SmoothedSumMellin.integral_norm_comp (wt : ℝ → ℂ) (s : ℂ) {n : ℝ} (hn : 0 < n) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt (t * n)‖
      = n ^ (-s.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ := by sorry
