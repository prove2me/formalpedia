-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_crude_budget
-- name    : OAI.RVM.PhaseFlowOn.closedEulerian_crude_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:17:03.111914+00:00
-- url     : https://prove2.me/theorems/1f2aa118-7631-4d1b-8f2c-5af4e5a77756
-- title:
--   OAI.RVM.PhaseFlowOn.closedEulerian_crude_budget: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.closedEulerian_crude_budget` of [lean/OAI/Analysis/VlasovMaxwell/Flow/ClosedEulerianCrudeBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Flow/ClosedEulerianCrudeBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.closedEulerian_crude_budget {s : Solution} {T a b I : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
--       (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
--       (hJ : Icc a b⊆Icc 0 T) (hI : b-a≤I) (hr : 0≤B.rmin) (hq : 0<B.qmin) :
--       coneOccupation F.flow zX T s.f
--         (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
--         ENNReal.ofReal (I+B.rmax)/ENNReal.ofReal B.qmin*
--           ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.closedBinEulerian`, `OAI.RVM.coneOccupation` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direct_source_large_radius`, `OAI.RVM.Admissible.direct_source_relative_budget`, `OAI.RVM.Admissible.representative_pure_occupation`, `OAI.RVM.Admissible.source_majorant_large_radius`, `OAI.RVM.Admissible.source_majorant_relative_budget`, `OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget`, `OAI.RVM.PhaseFlowOn.closedEulerian_joint_large_budget` and `OAI.RVM.PhaseFlowOn.closedEulerian_shared_budget` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Flow/ClosedEulerianCrudeBudget.lean (declaration OAI.RVM.PhaseFlowOn.closedEulerian_crude_budget)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.closedEulerian_crude_budget {s : Solution} {T a b I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b⊆Icc 0 T) (hI : b-a≤I) (hr : 0≤B.rmin) (hq : 0<B.qmin) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      ENNReal.ofReal (I+B.rmax)/ENNReal.ofReal B.qmin*
        ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)) := by
  sorry

end RVM

end

end OAI
end
