-- Prove2me | Theorems.Thm_OAI_FKCRT_Inventory_actual_map_tests
-- name    : OAI.FKCRT.Inventory.actual_map_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T18:23:56.899997+00:00
-- url     : https://prove2.me/theorems/640173ba-5fdb-4795-9ff6-2887b2748ba8
-- title:
--   OAI.FKCRT.Inventory.actual_map_tests: intermediate lemma from OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FKCRT.Inventory.actual_map_tests` of [lean/OAI/Probability/FKMaps/FKMaps/Convergence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/Convergence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FKCRT.Inventory`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology BigOperators ENNReal NNReal`, `open FKCRT.TreeCoding`):
--
--   ```lean
--   theorem actual_map_tests (P : Parameters)
--       {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
--       {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) μ)
--       (hI : iIndepFun (fun i ω t => B i t ω) μ)
--       (F : FKCRT.MetricMeasureData → ℝ) (hF : FKCRT.IsGHPTest F) :
--       Tendsto (fun n => ∫ x,FKCRT.markedMapTest (edgeScale P n) n F x ∂actualDrawLaw P n)
--         atTop (𝓝 (FKCRT.brownianExpectation μ B F))
--   ```
--
--   **Definitions.** The statement is written with `OAI.FKCRT.Inventory.ActualDraw`, `OAI.FKCRT.Inventory.CoreLabel`, `OAI.FKCRT.Inventory.Parameters`, `OAI.FKCRT.TreeCoding.Code` and `OAI.FKCRT.Inventory.CoreLabel.instMeasurableSpace` (definitions bundle `OAIQ021F000` of this split); `OAI.FKCRT.TreeCoding.instMeasurableSpaceCode` (definitions bundle `OAIQ021F003` of this split); `OAI.FKCRT.markedMapTest`, `OAI.FKCRT.Inventory.actualDrawLaw` and `OAI.FKCRT.Inventory.edgeScale` (definitions bundle `OAIQ021F004` of this split); `OAI.FKCRT.IsGHPTest`, `OAI.FKCRT.MetricMeasureData` and `OAI.FKCRT.brownianExpectation` (the published bundle `Def_FKCRT`).
--
--   **Used by.** The proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt` of this split imports it.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/Convergence.lean (declaration OAI.FKCRT.Inventory.actual_map_tests)

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
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

theorem actual_map_tests (P : Parameters)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) μ)
    (hI : iIndepFun (fun i ω t => B i t ω) μ)
    (F : FKCRT.MetricMeasureData → ℝ) (hF : FKCRT.IsGHPTest F) :
    Tendsto (fun n => ∫ x,FKCRT.markedMapTest (edgeScale P n) n F x ∂actualDrawLaw P n)
      atTop (𝓝 (FKCRT.brownianExpectation μ B F)) := by
  sorry

end FKCRT.Inventory
end

end OAI
end
