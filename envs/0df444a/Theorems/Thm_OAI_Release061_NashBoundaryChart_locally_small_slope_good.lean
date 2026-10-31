-- Prove2me | Theorems.Thm_OAI_Release061_NashBoundaryChart_locally_small_slope_good
-- name    : OAI.Release061.NashBoundaryChart.locally_small_slope_good
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:46:45.730417+00:00
-- url     : https://prove2.me/theorems/82adc41e-f2c9-4235-999b-b0fdd7747fa5
-- title:
--   OAI.Release061.NashBoundaryChart.locally_small_slope_good: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.NashBoundaryChart.locally_small_slope_good` of [lean/OAI/Analysis/SymmetricDomains/LocallySmallSlopeGood.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/LocallySmallSlopeGood.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology Metric MeasureTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem NashBoundaryChart.locally_small_slope_good {d m N : ℕ} {U V : Set (Affine N)}
--       {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine N}
--       (c : NashBoundaryChart (m := m) U V B q) :
--       ∃ W : Set (Fin d → ℝ), IsOpen W ∧ c.center ∈ W ∧
--         volume {x | x ∈ W ∧ ¬ SmallSlopeGoodNashBoundary m U V B q x} = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.NashBoundaryChart` and `OAI.Release061.SmallSlopeGoodNashBoundary` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.Affine` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.NashPatch.null_nonsmallgood_generic` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/LocallySmallSlopeGood.lean (declaration OAI.Release061.NashBoundaryChart.locally_small_slope_good)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem NashBoundaryChart.locally_small_slope_good {d m N : ℕ} {U V : Set (Affine N)}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine N}
    (c : NashBoundaryChart (m := m) U V B q) :
    ∃ W : Set (Fin d → ℝ), IsOpen W ∧ c.center ∈ W ∧
      volume {x | x ∈ W ∧ ¬ SmallSlopeGoodNashBoundary m U V B q x} = 0 := by
  sorry

end Release061

end

end OAI
end
