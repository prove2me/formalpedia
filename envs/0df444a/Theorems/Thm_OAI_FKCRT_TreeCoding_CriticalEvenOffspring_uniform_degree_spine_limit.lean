-- Prove2me | Theorems.Thm_OAI_FKCRT_TreeCoding_CriticalEvenOffspring_uniform_degree_spine_limit
-- name    : OAI.FKCRT.TreeCoding.CriticalEvenOffspring.uniform_degree_spine_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T18:31:11.166293+00:00
-- url     : https://prove2.me/theorems/d461847f-db75-40c5-865b-4f827870a929
-- title:
--   OAI.FKCRT.TreeCoding.CriticalEvenOffspring.uniform_degree_spine_limit (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.uniform_degree_spine_limit` of [lean/OAI/Probability/FKMaps/FKMaps/MarkedSpines.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/MarkedSpines.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FKCRT.TreeCoding`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology BigOperators ENNReal NNReal`):
--
--   ```lean
--   theorem CriticalEvenOffspring.uniform_degree_spine_limit (p : CriticalEvenOffspring)
--       {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
--       {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {ε : ℝ} (hε : 0<ε) :
--       Tendsto (fun n => (p.codeLaw n).real {d | ∃ v<2*n+1,
--         ε*Real.sqrt ((2*n+1:ℕ):ℝ)< |codeSpineSum (fun z => (z.1:ℝ)) d v-
--           (p.variance+1)*height d.val v|}) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FKCRT.TreeCoding.Code`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring`, `OAI.FKCRT.TreeCoding.IsTreeCode` and `OAI.FKCRT.TreeCoding.height` (definitions bundle `OAIQ021F000` of this split); `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.variance` (definitions bundle `OAIQ021F002` of this split); `OAI.FKCRT.TreeCoding.instMeasurableSpaceCode` (definitions bundle `OAIQ021F003` of this split); `OAI.FKCRT.TreeCoding.codeSpineSum` and `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.codeLaw` (definitions bundle `OAIQ021F004` of this split).
--
--   **Used by.** The proof of `OAI.FKCRT.Inventory.actual_map_tests` of this split imports it.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/MarkedSpines.lean (declaration OAI.FKCRT.TreeCoding.CriticalEvenOffspring.uniform_degree_spine_limit)

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
namespace FKCRT.TreeCoding

theorem CriticalEvenOffspring.uniform_degree_spine_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real {d | ∃ v<2*n+1,
      ε*Real.sqrt ((2*n+1:ℕ):ℝ)< |codeSpineSum (fun z => (z.1:ℝ)) d v-
        (p.variance+1)*height d.val v|}) atTop (𝓝 0) := by
  sorry

end FKCRT.TreeCoding
end

end OAI
end
