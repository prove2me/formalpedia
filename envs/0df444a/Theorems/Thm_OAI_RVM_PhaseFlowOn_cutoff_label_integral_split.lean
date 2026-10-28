-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_cutoff_label_integral_split
-- name    : OAI.RVM.PhaseFlowOn.cutoff_label_integral_split
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:17:47.881023+00:00
-- url     : https://prove2.me/theorems/3695053b-be99-4758-8d89-9294753be491
-- title:
--   OAI.RVM.PhaseFlowOn.cutoff_label_integral_split: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.cutoff_label_integral_split` of [lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.cutoff_label_integral_split {s : Solution} {T : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
--       (Q : Set (Fin 4→ℕ)) {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) :
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
--         (actualLabelCutoffCost s F.flow zX T Q p)‖)≤
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
--         (partialCutoffLabelCost s F.flow zX T Q
--           (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)+
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
--         (partialCutoffLabelCost s F.flow zX T Q
--           (fun p=>cutoffGeometryTangent (branchTime F.flow zX p.2 T p.1-p.1) (branchRate F.flow zX p.2 T p.1)
--             (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2) (velocity (F.flow p.2 p.1).2)
--             (branchDirection F.flow zX p.2 T p.1)) p)‖)+
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
--         (partialCutoffLabelCost s F.flow zX T Q
--           (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
--             (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.actualLabelCutoffCost`, `OAI.RVM.branchDirection`, `OAI.RVM.branchRate`, `OAI.RVM.branchTime`, `OAI.RVM.cutoffGeometryTangent`, `OAI.RVM.cutoffReceiverTangent`, `OAI.RVM.cutoffSourceTangent`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.lorentzField` and `OAI.RVM.partialCutoffLabelCost` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.bulk_selected_family_uniform` and `OAI.RVM.Admissible.direction_selected_bulk_log_bound` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean (declaration OAI.RVM.PhaseFlowOn.cutoff_label_integral_split)

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

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.cutoff_label_integral_split {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (actualLabelCutoffCost s F.flow zX T Q p)‖)≤
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q
        (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)+
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q
        (fun p=>cutoffGeometryTangent (branchTime F.flow zX p.2 T p.1-p.1) (branchRate F.flow zX p.2 T p.1)
          (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2) (velocity (F.flow p.2 p.1).2)
          (branchDirection F.flow zX p.2 T p.1)) p)‖)+
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q
        (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
          (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
