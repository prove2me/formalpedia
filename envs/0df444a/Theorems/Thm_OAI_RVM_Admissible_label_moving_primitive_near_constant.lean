-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_label_moving_primitive_near_constant
-- name    : OAI.RVM.Admissible.label_moving_primitive_near_constant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:08:42.742987+00:00
-- url     : https://prove2.me/theorems/e413be8e-1d6f-4804-9b54-d755b1fb389e
-- title:
--   OAI.RVM.Admissible.label_moving_primitive_near_constant: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.label_moving_primitive_near_constant` of [lean/OAI/Analysis/VlasovMaxwell/Population/SelectedReceiverWeightBoundFinite.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedReceiverWeightBoundFinite.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.label_moving_primitive_near_constant {d : Datum} (hd₀ : Admissible d) :
--       ∃C : ℝ, 0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
--         ∀(zX : Phase) (J : Set ℝ) (w p θ φ : ℝ) (k : Fin 4→ℕ),
--         MeasurableSet J → J⊆Icc 0 T → 0<w → 0≤p → 0≤θ → 0<φ → φ≤1 → θ≤φ →
--         φ^2/2≤(representativeClosedBin T w k).Dmin →
--         (representativeClosedBin T w k).Dmax≤8*φ^2 →
--         (representativeClosedBin T w k).dmax≤8*θ^2 →
--         (representativeClosedBin T w k).qmax≤p →
--         (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
--         (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
--         ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
--         (∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
--           ENNReal.ofReal ‖labelConeKernel s F.flow zX T
--             (projectedDyadicRateKernel F.flow zX T k
--             (fun t=>angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2)) z‖)≤
--         (∫⁻t in J,ENNReal.ofReal (b t)*ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
--           ENNReal.ofReal (C*(p*θ)^3*φ/w*
--             (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
--               (representativeClosedBin T w k).rmin))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.angularDerivativeCLM`, `OAI.RVM.labelConeKernel`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.lorentzField`, `OAI.RVM.projectedDyadicRateKernel`, `OAI.RVM.representativeClosedBin` and `OAI.RVM.ClosedConeBin` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.selected_moving_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedReceiverWeightBoundFinite.lean (declaration OAI.RVM.Admissible.label_moving_primitive_near_constant)

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

lemma Admissible.label_moving_primitive_near_constant {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w p θ φ : ℝ) (k : Fin 4→ℕ),
      MeasurableSet J → J⊆Icc 0 T → 0<w → 0≤p → 0≤θ → 0<φ → φ≤1 → θ≤φ →
      φ^2/2≤(representativeClosedBin T w k).Dmin →
      (representativeClosedBin T w k).Dmax≤8*φ^2 →
      (representativeClosedBin T w k).dmax≤8*θ^2 →
      (representativeClosedBin T w k).qmax≤p →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T
          (projectedDyadicRateKernel F.flow zX T k
          (fun t=>angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2)) z‖)≤
      (∫⁻t in J,ENNReal.ofReal (b t)*ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*(p*θ)^3*φ/w*
          (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
            (representativeClosedBin T w k).rmin)) := by
  sorry

end RVM

end

end OAI
end
