-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_selectedConeTriangle_norm_transfer
-- name    : OAI.RVM.PhaseFlowOn.selectedConeTriangle_norm_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:07.326163+00:00
-- url     : https://prove2.me/theorems/60cf160c-2303-4a68-9737-36ee7146b917
-- title:
--   OAI.RVM.PhaseFlowOn.selectedConeTriangle_norm_transfer: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.selectedConeTriangle_norm_transfer` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/SelectedConeTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SelectedConeTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.selectedConeTriangle_norm_transfer {s : Solution} {T : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (Q : Set (Fin 4→ℕ))
--       {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T))
--       {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
--         (labelSelectedCutoff F.flow zX T Q p • labelConeKernel s F.flow zX T A p)‖)=
--         ∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q A W J p‖ ∂trianglePhaseMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeCoordinate`, `OAI.RVM.ConeKernelState`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.TrianglePhase`, `OAI.RVM.coneKernelInterior`, `OAI.RVM.labelConeKernel`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.labelSelectedCutoff`, `OAI.RVM.selectedConeTriangle` and `OAI.RVM.trianglePhaseMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.bulk_selected_family_uniform`, `OAI.RVM.Admissible.direction_remainder_label_log_bound`, `OAI.RVM.Admissible.direction_unselected_label_log_bound`, `OAI.RVM.Admissible.force_bulk_receiver_residual_uniform`, `OAI.RVM.Admissible.unselected_label_uniform` and `OAI.RVM.PhaseFlowOn.unselected_source_label_physical_sum` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SelectedConeTransfer.lean (declaration OAI.RVM.PhaseFlowOn.selectedConeTriangle_norm_transfer)

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
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.selectedConeTriangle_norm_transfer {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Q p • labelConeKernel s F.flow zX T A p)‖)=
      ∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q A W J p‖ ∂trianglePhaseMeasure := by
  sorry

end RVM

end

end OAI
end
