-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direction_receiverCutoff_label_log_bound
-- name    : OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:06:45.602631+00:00
-- url     : https://prove2.me/theorems/9eb03fa4-e6b6-48c1-a622-5c86a8f0085d
-- title:
--   OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direction_receiverCutoff_label_log_bound {d : Datum} (hd₀ : Admissible d) :
--       ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) → 0≤T →
--         ∀(zX : Phase) (J : Set ℝ) (w P : ℝ) (hw : 0<w),
--         MeasurableSet J → J⊆Icc 0 T → 0<P → 1≤Real.log (2+P) →
--         (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
--         (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
--         (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
--           (labelReceiverTime F.flow zX T p)
--           (partialCutoffLabelCost s F.flow zX T (directionSelection T)
--             (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
--               (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖)≤
--         (∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
--           ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.branchRate`, `OAI.RVM.branchTime`, `OAI.RVM.cutoffReceiverTangent`, `OAI.RVM.directionSelection`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.lorentzField`, `OAI.RVM.partialCutoffLabelCost`, `OAI.RVM.prefixAngularMultiplier` and `OAI.RVM.prefixMomentumForce` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_selected_bulk_log_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean (declaration OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound)

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

lemma Admissible.direction_receiverCutoff_label_log_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) → 0≤T →
      ∀(zX : Phase) (J : Set ℝ) (w P : ℝ) (hw : 0<w),
      MeasurableSet J → J⊆Icc 0 T → 0<P → 1≤Real.log (2+P) →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T (directionSelection T)
          (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
            (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖)≤
      (∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
