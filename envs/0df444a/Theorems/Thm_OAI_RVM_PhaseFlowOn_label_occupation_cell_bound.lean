-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_label_occupation_cell_bound
-- name    : OAI.RVM.PhaseFlowOn.label_occupation_cell_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:18:18.604567+00:00
-- url     : https://prove2.me/theorems/a70a22fc-04cc-421d-9123-2f2eab4dd0f5
-- title:
--   OAI.RVM.PhaseFlowOn.label_occupation_cell_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.label_occupation_cell_bound` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/ObservationCone.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ObservationCone.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open scoped Topology ContDiff NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`):
--
--   ```lean
--   lemma PhaseFlowOn.label_occupation_cell_bound {s : Solution} {T t p D : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (ht : t ∈ Icc 0 T)
--       {H : Phase → Set ℝ}
--       (hduration : ∀ z, volume (H z) ≤ ENNReal.ofReal D)
--       (hmom : ∀ z, (H z).Nonempty → p≤q (F.flow z t).2) :
--       ENNReal.ofReal p * labelOccupation (fun z => s.f (0,z)) H ≤
--         ENNReal.ofReal D * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.labelOccupation` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direction_stable_closed_cell_bound`, `OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude` and `OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ObservationCone.lean (declaration OAI.RVM.PhaseFlowOn.label_occupation_cell_bound)

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
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

lemma PhaseFlowOn.label_occupation_cell_bound {s : Solution} {T t p D : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (ht : t ∈ Icc 0 T)
    {H : Phase → Set ℝ}
    (hduration : ∀ z, volume (H z) ≤ ENNReal.ofReal D)
    (hmom : ∀ z, (H z).Nonempty → p≤q (F.flow z t).2) :
    ENNReal.ofReal p * labelOccupation (fun z => s.f (0,z)) H ≤
      ENNReal.ofReal D * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  sorry

end RVM

end

end OAI
end
