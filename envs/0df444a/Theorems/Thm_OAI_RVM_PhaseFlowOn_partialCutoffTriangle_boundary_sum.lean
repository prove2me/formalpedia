-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_partialCutoffTriangle_boundary_sum
-- name    : OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:18:42.544821+00:00
-- url     : https://prove2.me/theorems/88eeb43b-9d74-48c0-b6fb-c30afdb21992
-- title:
--   OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum` of [lean/OAI/Analysis/VlasovMaxwell/Population/PhysicalBinPhaseSet.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PhysicalBinPhaseSet.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.partialCutoffTriangle_boundary_sum {s : Solution} {T w : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
--       (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
--       (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
--       (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
--       (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
--       (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) :
--       (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J p‖ ∂trianglePhaseMeasure)≤
--         ∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator (fun k=>
--           ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k)
--             z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
--             ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J (z,v)‖ ∂volume
--             ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeCoordinate`, `OAI.RVM.ConeKernelState`, `OAI.RVM.CutoffState`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.TrianglePhase`, `OAI.RVM.coneBinMomentumSet`, `OAI.RVM.coneKernelInterior`, `OAI.RVM.dyadicSelectionBoundary`, `OAI.RVM.partialCutoffTriangle`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.prefixFlow`, `OAI.RVM.representativeClosedBin` and `OAI.RVM.trianglePhaseMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.q` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound`, `OAI.RVM.Admissible.direction_selected_bulk_log_bound` and `OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PhysicalBinPhaseSet.lean (declaration OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum)

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

lemma PhaseFlowOn.partialCutoffTriangle_boundary_sum {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) :
    (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J p‖ ∂trianglePhaseMeasure)≤
      ∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator (fun k=>
        ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k)
          z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
          ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J (z,v)‖ ∂volume
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  sorry

end RVM

end

end OAI
end
