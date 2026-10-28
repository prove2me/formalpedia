-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_selectedMultiplier_integrable
-- name    : OAI.RVM.PhaseFlowOn.selectedMultiplier_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:30.497989+00:00
-- url     : https://prove2.me/theorems/789acb96-f325-497a-a6cc-2bbd8bc6faaa
-- title:
--   OAI.RVM.PhaseFlowOn.selectedMultiplier_integrable: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.selectedMultiplier_integrable` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/InitialPuncturedCone.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/InitialPuncturedCone.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma PhaseFlowOn.selectedMultiplier_integrable {s : Solution} {T : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
--       (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
--       (hψb : ∀t∈Icc 0 T,|ψ t|≤1) {G G' : ℝ→Vec→L[ℝ]Vec}
--       (hG : Continuous G) (hG' : Continuous G') :
--       Integrable (selectedMultiplierForce s F.flow zX T Q ψ G) ∧
--         Integrable (selectedMultiplierCosts s F.flow zX T Q ψ G G')
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.selectedMultiplierCosts` and `OAI.RVM.selectedMultiplierForce` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/InitialPuncturedCone.lean (declaration OAI.RVM.PhaseFlowOn.selectedMultiplier_integrable)

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
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.selectedMultiplier_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) {G G' : ℝ→Vec→L[ℝ]Vec}
    (hG : Continuous G) (hG' : Continuous G') :
    Integrable (selectedMultiplierForce s F.flow zX T Q ψ G) ∧
      Integrable (selectedMultiplierCosts s F.flow zX T Q ψ G G') := by
  sorry

end RVM

end

end OAI
end
