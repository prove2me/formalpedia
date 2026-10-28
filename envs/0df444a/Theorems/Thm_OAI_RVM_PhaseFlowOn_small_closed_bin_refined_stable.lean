-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_small_closed_bin_refined_stable
-- name    : OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:55.923226+00:00
-- url     : https://prove2.me/theorems/8db8c967-5374-4069-9eca-5cdc82e8da5c
-- title:
--   OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable` of [lean/OAI/Analysis/VlasovMaxwell/Population/BinHits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/BinHits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal`, `open Set`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open scoped Topology ContDiff`, `open Set`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   lemma PhaseFlowOn.small_closed_bin_refined_stable {s : Solution}
--       {T M A P L a b massScale φ C p len I : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
--       (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
--       (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
--       (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len)
--       (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
--       (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
--       (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
--       (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
--       (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
--       (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax) (hrad : B.rmax ≤ len)
--       (hd : B.dmax ≤ φ^2/32)
--       (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
--       (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
--       (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
--       (hI : 0 < I) :
--       ENNReal.ofReal len * ENNReal.ofReal (p/256) *
--           labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) ≤
--         ENNReal.ofReal (40*B.rmax) *
--           (ENNReal.ofReal len * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) +
--             ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 4
--               (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.closedBinHits`, `OAI.RVM.jointEnergyBudget`, `OAI.RVM.labelOccupation` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget` and `OAI.RVM.PhaseFlowOn.closedEulerian_shared_budget` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/BinHits.lean (declaration OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable)

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

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

lemma PhaseFlowOn.small_closed_bin_refined_stable {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax) (hrad : B.rmax ≤ len)
    (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
    (hI : 0 < I) :
    ENNReal.ofReal len * ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) ≤
      ENNReal.ofReal (40*B.rmax) *
        (ENNReal.ofReal len * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) +
          ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 4
            (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf)) := by
  sorry

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

open Set MeasureTheory
open scoped ENNReal

end RVM

end

end OAI
end
