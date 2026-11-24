-- Prove2me | Theorems.Thm_GlobalTheory_SmoothedSumMellin_weight_bound
-- name    : GlobalTheory.SmoothedSumMellin.weight_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:18:47.104594+00:00
-- url     : https://prove2.me/theorems/9bc499b4-6c02-443d-90eb-3400d7517c36
-- title:
--   Smoothed Sum Mellin: weight bound
-- statement:
--   The Smoothed Sum Mellin construction uses the weight bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean#L9-L26

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

theorem GlobalTheory.SmoothedSumMellin.weight_bound {wt : ℝ → ℂ} (hc : Continuous wt) {a b : ℝ}
    (hs : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 < y → ‖wt y‖ ≤ M * y ^ (-2 : ℝ) := by sorry
