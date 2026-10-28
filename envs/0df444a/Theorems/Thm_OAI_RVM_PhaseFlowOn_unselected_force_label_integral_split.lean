-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_unselected_force_label_integral_split
-- name    : OAI.RVM.PhaseFlowOn.unselected_force_label_integral_split
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:20:28.409621+00:00
-- url     : https://prove2.me/theorems/6a57ede8-1233-4e2a-a874-3f0691b8320e
-- title:
--   OAI.RVM.PhaseFlowOn.unselected_force_label_integral_split: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.unselected_force_label_integral_split` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.unselected_force_label_integral_split {s : Solution} {T : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ))
--       {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
--         ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p)‖)≤
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
--         (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (transportOnlyConeKernel F.flow zX) p)‖)+
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
--         (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (sourceOnlyConeKernel s F.flow zX) p)‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.actualLabelSignedForce`, `OAI.RVM.labelConeKernel`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.labelSelectedCutoff`, `OAI.RVM.sourceOnlyConeKernel` and `OAI.RVM.transportOnlyConeKernel` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direction_unselected_label_log_bound` and `OAI.RVM.Admissible.unselected_label_uniform` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean (declaration OAI.RVM.PhaseFlowOn.unselected_force_label_integral_split)

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

lemma PhaseFlowOn.unselected_force_label_integral_split {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p)‖)≤
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (transportOnlyConeKernel F.flow zX) p)‖)+
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (sourceOnlyConeKernel s F.flow zX) p)‖) := by
  sorry

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end RVM

end

end OAI
end
