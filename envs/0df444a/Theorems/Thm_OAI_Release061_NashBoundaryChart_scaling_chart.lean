-- Prove2me | Theorems.Thm_OAI_Release061_NashBoundaryChart_scaling_chart
-- name    : OAI.Release061.NashBoundaryChart.scaling_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:47:09.828754+00:00
-- url     : https://prove2.me/theorems/1df95995-7804-4244-93e2-57b8514d3061
-- title:
--   OAI.Release061.NashBoundaryChart.scaling_chart: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.NashBoundaryChart.scaling_chart` of [lean/OAI/Analysis/SymmetricDomains/OffsetDerivative.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/OffsetDerivative.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061.NashBoundaryChart`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology Metric`, `open scoped Classical`):
--
--   ```lean
--   theorem scaling_chart (c : NashBoundaryChart (m := m) U V B q) {x}
--       (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
--       (hqi : Function.Injective (fderiv ℝ q x))
--       (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
--       Nonempty (NashBoundaryScalingChart c x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.NashBoundaryChart`, `OAI.Release061.NashBoundaryScalingChart` and `OAI.Release061.NashBoundaryChart.GoodAt` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.Affine` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.original_supported_hermitian_model` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/OffsetDerivative.lean (declaration OAI.Release061.NashBoundaryChart.scaling_chart)

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

open Set Filter Topology Metric
open scoped Classical

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

theorem scaling_chart (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Nonempty (NashBoundaryScalingChart c x) := by
  sorry
end NashBoundaryChart

end Release061

end

end OAI
end
