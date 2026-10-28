-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_unselected_source_label_physical_sum
-- name    : OAI.RVM.PhaseFlowOn.unselected_source_label_physical_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:20:25.571997+00:00
-- url     : https://prove2.me/theorems/415cb240-cca2-4f18-883d-14b6533cf047
-- title:
--   OAI.RVM.PhaseFlowOn.unselected_source_label_physical_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.unselected_source_label_physical_sum` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.unselected_source_label_physical_sum {s : Solution} {T w P : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
--       (hw : 0<w) (zX : Phase) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
--       (hq : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
--       (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
--       (hP : 1≤P) (hL : 1≤Real.log (2+P))
--       (hsource : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) :
--       let X := fun t=>(prefixFlow F.flow T zX t).1
--       let V := fun t=>(prefixFlow F.flow T zX t).2
--       let Q := directionSelection T
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
--         (labelReceiverTime F.flow zX T p)
--         (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (sourceOnlyConeKernel s F.flow zX) p)‖)≤
--       ENNReal.ofReal 64*(∑'k,directionRemaining.indicator (fun k=>∫⁻z : ConeCoordinate,
--         physicalSourceMajorantDensity s X V (representativeClosedBin T w k) z
--           ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)+
--       (∑'k,(directionSourceFar T w P).indicator (fun k=>∫⁻z : ConeCoordinate,
--         physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
--           ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)+
--       (∑'k,(directionSourceLow w).indicator (fun k=>∫⁻z : ConeCoordinate,
--         physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
--           ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.directionRemaining`, `OAI.RVM.directionSelection`, `OAI.RVM.directionSourceFar`, `OAI.RVM.directionSourceLow`, `OAI.RVM.labelConeKernel`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.labelSelectedCutoff`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalProjectedSourceDensity`, `OAI.RVM.physicalSourceMajorantDensity`, `OAI.RVM.prefixAngularMultiplier`, `OAI.RVM.prefixFlow`, `OAI.RVM.representativeClosedBin` and `OAI.RVM.sourceOnlyConeKernel` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_unselected_label_log_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean (declaration OAI.RVM.PhaseFlowOn.unselected_source_label_physical_sum)

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

lemma PhaseFlowOn.unselected_source_label_physical_sum {s : Solution} {T w P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (hw : 0<w) (zX : Phase) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hq : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (hP : 1≤P) (hL : 1≤Real.log (2+P))
    (hsource : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    let Q := directionSelection T
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
      (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (sourceOnlyConeKernel s F.flow zX) p)‖)≤
    ENNReal.ofReal 64*(∑'k,directionRemaining.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalSourceMajorantDensity s X V (representativeClosedBin T w k) z
        ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)+
    (∑'k,(directionSourceFar T w P).indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)+
    (∑'k,(directionSourceLow w).indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) J) k) := by
  sorry

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end RVM

end

end OAI
end
