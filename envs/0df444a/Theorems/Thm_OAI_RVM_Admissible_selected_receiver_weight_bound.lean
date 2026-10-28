-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_selected_receiver_weight_bound
-- name    : OAI.RVM.Admissible.selected_receiver_weight_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:11:47.061468+00:00
-- url     : https://prove2.me/theorems/12b1405c-d96b-4eb3-84e0-efa3f9aa84b8
-- title:
--   OAI.RVM.Admissible.selected_receiver_weight_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.selected_receiver_weight_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/SelectedReceiverWeightBoundFinite.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedReceiverWeightBoundFinite.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.selected_receiver_weight_bound {d : Datum} (hd : Admissible d) :
--       ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
--         ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
--         (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
--         (∀k∈Q,cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
--           sourceRepresentative (k 0)*cappedRepresentative (k 1)*
--             Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
--         MeasurableSet J → J⊆Icc 0 T → 0<w →
--         (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
--         (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
--         ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
--         (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularMultiplierCLM w (F.flow zX (labelReceiverTime F.flow zX T p)).2
--           (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖)≤
--         (∫⁻t in J,ENNReal.ofReal |b t|)*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.actualLabelRatePrimitive`, `OAI.RVM.angularMultiplierCLM`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.labelWeight` and `OAI.RVM.sourceRepresentative` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_physical_family_log_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedReceiverWeightBoundFinite.lean (declaration OAI.RVM.Admissible.selected_receiver_weight_bound)

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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.selected_receiver_weight_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
      (∀k∈Q,cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularMultiplierCLM w (F.flow zX (labelReceiverTime F.flow zX T p)).2
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖)≤
      (∫⁻t in J,ENNReal.ofReal |b t|)*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2) := by
  sorry

end RVM

end

end OAI
end
