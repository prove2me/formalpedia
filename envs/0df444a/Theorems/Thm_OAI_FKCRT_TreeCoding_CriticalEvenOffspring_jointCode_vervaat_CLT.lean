-- Prove2me | Theorems.Thm_OAI_FKCRT_TreeCoding_CriticalEvenOffspring_jointCode_vervaat_CLT
-- name    : OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T18:25:11.691842+00:00
-- url     : https://prove2.me/theorems/3263ae22-0cf1-4883-802b-855ac57f88b9
-- title:
--   OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT: intermediate lemma from OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT` of [lean/OAI/Probability/FKMaps/FKMaps/HeightTightness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/HeightTightness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FKCRT.TreeCoding`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology BigOperators ENNReal NNReal`):
--
--   ```lean
--   theorem CriticalEvenOffspring.jointCode_vervaat_CLT (p : CriticalEvenOffspring)
--       {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
--       {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
--       TendstoInDistribution (fun n (d : Code (2*n+1)) => jointCode p.sigma d) atTop
--         (fun ω => diagonalPath (vervaat (bridgePath B ω))) p.codeLaw P
--   ```
--
--   **Definitions.** The statement is written with `OAI.FKCRT.TreeCoding.Code` and `OAI.FKCRT.TreeCoding.CriticalEvenOffspring` (definitions bundle `OAIQ021F000` of this split); `OAI.FKCRT.TreeCoding.bridgePath`, `OAI.FKCRT.TreeCoding.diagonalPath`, `OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitIntervalProd_solutions`, `OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitIntervalProd_solutions` and `OAI.FKCRT.TreeCoding.vervaat` (definitions bundle `OAIQ021F001` of this split); `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.sigma` (definitions bundle `OAIQ021F002` of this split); `OAI.FKCRT.TreeCoding.instMeasurableSpaceCode` and `OAI.FKCRT.TreeCoding.jointCode` (definitions bundle `OAIQ021F003` of this split); `OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw` and `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.codeLaw` (definitions bundle `OAIQ021F004` of this split).
--
--   **Used by.** The proofs of `OAI.FKCRT.Inventory.actualHeight_CLT` and `OAI.FKCRT.Inventory.actual_map_tests` of this split import it.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FKMaps/FKMaps/HeightTightness.lean (declaration OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT)

import Mathlib
import Definitions.Def_OAIQ021F004

section

attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_12_r78ecef_1 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩
attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitIntervalProd_solutions
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitIntervalProd_solutions
theorem CriticalEvenOffspring.jointCode_vervaat_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    TendstoInDistribution (fun n (d : Code (2*n+1)) => jointCode p.sigma d) atTop
      (fun ω => diagonalPath (vervaat (bridgePath B ω))) p.codeLaw P := by
  sorry

end FKCRT.TreeCoding
end

end OAI
end
