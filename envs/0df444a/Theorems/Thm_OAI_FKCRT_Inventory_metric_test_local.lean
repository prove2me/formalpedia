-- Prove2me | Theorems.Thm_OAI_FKCRT_Inventory_metric_test_local
-- name    : OAI.FKCRT.Inventory.metric_test_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T18:25:25.843447+00:00
-- url     : https://prove2.me/theorems/f818a020-278e-480b-9983-9d07288ef7ca
-- title:
--   OAI.FKCRT.Inventory.metric_test_local: intermediate lemma from OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FKCRT.Inventory.metric_test_local` of [lean/OAI/Probability/FKMaps/FKMaps/MetricLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/MetricLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FKCRT.Inventory`, with `open List Set MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators ENNReal Topology NNReal`, `open FKCRT.TreeCoding`):
--
--   ```lean
--   theorem metric_test_local (P : Parameters) (F : FKCRT.MetricMeasureData → ℝ)
--       (hF : FKCRT.IsGHPTest F) (ε : ℝ) (hε : 0<ε) (f : C(unitInterval,ℝ)) :
--       ∃ r : ℝ,0 < r ∧ ∃ a : ℝ,0<a ∧ ∃ N : ℕ,∀ n≥N,∀ x : ActualDraw n,
--         dist (actualHeight P n x) f < r → x∉metricBad P n a →
--         |FKCRT.markedMapTest (edgeScale P n) n F x-F (FKCRT.treeSpace (actualHeight P n x))| ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.FKCRT.Inventory.ActualDraw` and `OAI.FKCRT.Inventory.Parameters` (definitions bundle `OAIQ021F000` of this split); `OAI.FKCRT.markedMapTest`, `OAI.FKCRT.Inventory.actualHeight`, `OAI.FKCRT.Inventory.edgeScale` and `OAI.FKCRT.Inventory.metricBad` (definitions bundle `OAIQ021F004` of this split); `OAI.FKCRT.IsGHPTest`, `OAI.FKCRT.MetricMeasureData` and `OAI.FKCRT.treeSpace` (the published bundle `Def_FKCRT`).
--
--   **Used by.** The proof of `OAI.FKCRT.Inventory.actual_map_tests` of this split imports it.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/MetricLimit.lean (declaration OAI.FKCRT.Inventory.metric_test_local)

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_OAIQ021F004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

theorem metric_test_local (P : Parameters) (F : FKCRT.MetricMeasureData → ℝ)
    (hF : FKCRT.IsGHPTest F) (ε : ℝ) (hε : 0<ε) (f : C(unitInterval,ℝ)) :
    ∃ r : ℝ,0 < r ∧ ∃ a : ℝ,0<a ∧ ∃ N : ℕ,∀ n≥N,∀ x : ActualDraw n,
      dist (actualHeight P n x) f < r → x∉metricBad P n a →
      |FKCRT.markedMapTest (edgeScale P n) n F x-F (FKCRT.treeSpace (actualHeight P n x))| ≤ ε := by
  sorry

end FKCRT.Inventory
end

end OAI
end
