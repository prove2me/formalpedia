-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_partialCutoffLabelCost_triangle
-- name    : OAI.RVM.PhaseFlowOn.partialCutoffLabelCost_triangle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:18:24.136756+00:00
-- url     : https://prove2.me/theorems/08e41db5-ec6d-4cb2-a638-f27b3223b897
-- title:
--   OAI.RVM.PhaseFlowOn.partialCutoffLabelCost_triangle: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.partialCutoffLabelCost_triangle` of [lean/OAI/Analysis/VlasovMaxwell/Population/PhysicalBinPhaseSet.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PhysicalBinPhaseSet.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.partialCutoffLabelCost_triangle {s : Solution} {T : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
--       (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
--       (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
--       (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
--         (partialCutoffLabelCost s F.flow zX T Q (H ∘ labelKernelState F.flow zX T) p)‖)=
--         ∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J p‖ ∂trianglePhaseMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeCoordinate`, `OAI.RVM.ConeKernelState`, `OAI.RVM.CutoffState`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.TrianglePhase`, `OAI.RVM.coneKernelInterior`, `OAI.RVM.labelKernelState`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.partialCutoffLabelCost`, `OAI.RVM.partialCutoffTriangle` and `OAI.RVM.trianglePhaseMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.bulk_selected_family_uniform`, `OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound`, `OAI.RVM.Admissible.direction_selected_bulk_log_bound` and `OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PhysicalBinPhaseSet.lean (declaration OAI.RVM.PhaseFlowOn.partialCutoffLabelCost_triangle)

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

lemma PhaseFlowOn.partialCutoffLabelCost_triangle {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q (H ∘ labelKernelState F.flow zX T) p)‖)=
      ∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J p‖ ∂trianglePhaseMeasure := by
  sorry

end RVM

end

end OAI
end
