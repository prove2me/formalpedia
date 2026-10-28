-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_bulkRemainder_selected_sum
-- name    : OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:16:35.91978+00:00
-- url     : https://prove2.me/theorems/815684a0-dbc6-4b2e-8565-94f7432e52b4
-- title:
--   OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum` of [lean/OAI/Analysis/VlasovMaxwell/Population/SpatialEstimates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SpatialEstimates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`, `open Set Filter Metric MeasureTheory _root_.Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.bulkRemainder_selected_sum {s : Solution} {T P M A w I : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
--       {a b : ℝ} (ha : 0≤a) (hb : b≤T)
--       (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
--       (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
--       {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1) :
--       (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
--         (remainderConeKernel s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
--         ENNReal.ofReal 147*(∑'k : Fin 4→ℕ,(centralIndexSector P).indicator
--           (fun k=>representativeCentralCost s F zX w k a b) k)+
--         ENNReal.ofReal 15424*(∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
--           (fun k=>representativeReceiverCost s F zX w k a b (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.TrianglePhase`, `OAI.RVM.bulkSelection`, `OAI.RVM.centralIndexSector`, `OAI.RVM.prefixMomentumForce`, `OAI.RVM.remainderConeKernel`, `OAI.RVM.representativeCentralCost`, `OAI.RVM.representativeReceiverCost`, `OAI.RVM.representativeSelected`, `OAI.RVM.representativeSmallSector`, `OAI.RVM.selectedConeTriangle` and `OAI.RVM.trianglePhaseMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.bulk_remainder_uniform` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SpatialEstimates.lean (declaration OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum)

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

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

lemma PhaseFlowOn.bulkRemainder_selected_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
    {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1) :
    (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
      (remainderConeKernel s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal 147*(∑'k : Fin 4→ℕ,(centralIndexSector P).indicator
        (fun k=>representativeCentralCost s F zX w k a b) k)+
      ENNReal.ofReal 15424*(∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
        (fun k=>representativeReceiverCost s F zX w k a b (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) k) := by
  sorry

open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff

end RVM

end

end OAI
end
