-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_bulkReceiver_selected_sum
-- name    : OAI.RVM.PhaseFlowOn.bulkReceiver_selected_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:16:14.723148+00:00
-- url     : https://prove2.me/theorems/5ed26e0a-0fbe-483d-badc-37c8547d65f2
-- title:
--   OAI.RVM.PhaseFlowOn.bulkReceiver_selected_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.bulkReceiver_selected_sum` of [lean/OAI/Analysis/VlasovMaxwell/Population/BulkReceiverScalar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/BulkReceiverScalar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory Classical`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.bulkReceiver_selected_sum {s : Solution} {T P M A w I : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
--       {a b : ℝ} (ha : 0≤a) (hb : b≤T)
--       (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
--       (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
--       {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1)
--       {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C) :
--       (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
--         (coneReceiverCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
--         ENNReal.ofReal (2080000*C)*(∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
--           (fun k=>representativeReceiverCost s F zX w k a b (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.TrianglePhase`, `OAI.RVM.bulkSelection`, `OAI.RVM.coneReceiverCutoffTangent`, `OAI.RVM.dyadicFactor`, `OAI.RVM.partialCutoffTriangle`, `OAI.RVM.prefixMomentumForce`, `OAI.RVM.representativeReceiverCost`, `OAI.RVM.representativeSelected`, `OAI.RVM.representativeSmallSector` and `OAI.RVM.trianglePhaseMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.bulk_selected_family_uniform` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/BulkReceiverScalar.lean (declaration OAI.RVM.PhaseFlowOn.bulkReceiver_selected_sum)

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

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.bulkReceiver_selected_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
    {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C) :
    (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
      (coneReceiverCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal (2080000*C)*(∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
        (fun k=>representativeReceiverCost s F zX w k a b (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) k) := by
  sorry

end RVM

end

end OAI
end
