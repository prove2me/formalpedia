-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_baseline_budget
-- name    : OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:17:03.133076+00:00
-- url     : https://prove2.me/theorems/f72e24c0-c56b-4a67-b576-5f72de119a0a
-- title:
--   OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget` of [lean/OAI/Analysis/VlasovMaxwell/Flow/ClosedEulerianCrudeBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Flow/ClosedEulerianCrudeBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.closedEulerian_baseline_budget {s : Solution}
--       {T M A P L a b massScale φ C p len I : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
--       (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
--       (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
--       (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len) (hlenI : len≤I) (hab : b-a≤I)
--       (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
--       (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
--       (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
--       (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
--       (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
--       (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax)
--       (hd : B.dmax ≤ φ^2/32)
--       (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
--       (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
--       (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
--       coneOccupation F.flow zX T s.f
--         (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
--         ENNReal.ofReal (35512320*B.rmax/p*(1+I/len))*
--           ENNReal.ofReal (∫ x : Vec,totalEnergy s (0,x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.closedBinEulerian`, `OAI.RVM.coneOccupation` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.central_density_baseline_radial_sum`, `OAI.RVM.Admissible.projected_source_baseline_far` and `OAI.RVM.Admissible.representative_pure_occupation` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Flow/ClosedEulerianCrudeBudget.lean (declaration OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget)

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.closedEulerian_baseline_budget {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len) (hlenI : len≤I) (hab : b-a≤I)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax)
    (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      ENNReal.ofReal (35512320*B.rmax/p*(1+I/len))*
        ENNReal.ofReal (∫ x : Vec,totalEnergy s (0,x)) := by
  sorry

end RVM

end

end OAI
end
