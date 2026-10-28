-- Prove2me | Theorems.Thm_OAI_FKCRT_Inventory_actualHeight_CLT
-- name    : OAI.FKCRT.Inventory.actualHeight_CLT
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T18:25:56.82399+00:00
-- url     : https://prove2.me/theorems/857c5b15-934a-4634-8d5e-a3e193abbaf4
-- title:
--   OAI.FKCRT.Inventory.actualHeight_CLT: intermediate lemma from OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FKCRT.Inventory.actualHeight_CLT` of [lean/OAI/Probability/FKMaps/FKMaps/MetricLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/MetricLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FKCRT.Inventory`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology BigOperators ENNReal NNReal`, `open FKCRT.TreeCoding`):
--
--   ```lean
--   theorem actualHeight_CLT (P : Parameters)
--       {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
--       {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) μ)
--       (hI : iIndepFun (fun i ω t => B i t ω) μ) :
--       TendstoInDistribution (actualHeight P) atTop (excursionPath B) (actualDrawLaw P) μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.FKCRT.Inventory.ActualDraw`, `OAI.FKCRT.Inventory.CoreLabel`, `OAI.FKCRT.Inventory.Parameters`, `OAI.FKCRT.TreeCoding.Code` and `OAI.FKCRT.Inventory.CoreLabel.instMeasurableSpace` (definitions bundle `OAIQ021F000` of this split); `OAI.FKCRT.Inventory.instBorelSpaceContinuousMapElemRealUnitInterval_solutions`, `OAI.FKCRT.Inventory.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions` and `OAI.FKCRT.TreeCoding.excursionPath` (definitions bundle `OAIQ021F001` of this split); `OAI.FKCRT.Inventory.CoreLabel.markLaw` (definitions bundle `OAIQ021F002` of this split); `OAI.FKCRT.TreeCoding.instMeasurableSpaceCode` (definitions bundle `OAIQ021F003` of this split); `OAI.FKCRT.Inventory.actualDrawLaw`, `OAI.FKCRT.Inventory.actualHeight`, `OAI.FKCRT.Inventory.actualOffspring` and `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability` (definitions bundle `OAIQ021F004` of this split).
--
--   **Used by.** The proof of `OAI.FKCRT.Inventory.actual_map_tests` of this split imports it.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/MetricLimit.lean (declaration OAI.FKCRT.Inventory.actualHeight_CLT)

import Mathlib
import Definitions.Def_OAIQ021F004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding

attribute [local instance] OAI.FKCRT.Inventory.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions
attribute [local instance] OAI.FKCRT.Inventory.instBorelSpaceContinuousMapElemRealUnitInterval_solutions
theorem actualHeight_CLT (P : Parameters)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) μ)
    (hI : iIndepFun (fun i ω t => B i t ω) μ) :
    TendstoInDistribution (actualHeight P) atTop (excursionPath B) (actualDrawLaw P) μ := by
  sorry

end FKCRT.Inventory
end

end OAI
end
