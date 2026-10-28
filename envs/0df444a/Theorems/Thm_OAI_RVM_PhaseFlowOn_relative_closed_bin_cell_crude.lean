-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_relative_closed_bin_cell_crude
-- name    : OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:07.3877+00:00
-- url     : https://prove2.me/theorems/e0381299-64b1-42a2-888d-3d9bfc66cb35
-- title:
--   OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude` of [lean/OAI/Analysis/VlasovMaxwell/Population/RelativeClosedBinHitGeometry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/RelativeClosedBinHitGeometry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.relative_closed_bin_cell_crude {s : Solution}
--       {T M A P L lo hi a b c d massScale φ σ C p : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
--       (t₀ : ℝ) (ht₀ : t₀∈Icc c d) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
--       (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
--       (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
--       (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
--       (hm : 0 < massScale) (hφ : 0 < φ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hconst : 128 ≤ C)
--       (hlen : hi-lo ≤ (C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
--       (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
--       (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
--       (hr : 0 < B.rmin) (hDhi : B.Dmax ≤ 8*φ^2)
--       (helo : σ^2/2 ≤ B.emin) (hehi : B.emax ≤ 8*σ^2)
--       (hq : 4 ≤ σ*B.qmin) (hw : 4 ≤ σ*B.wmin)
--       (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
--       (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
--       ENNReal.ofReal (p/256) *
--           labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
--         ENNReal.ofReal (40*B.rmax*(1+φ/σ)) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.closedBinHits`, `OAI.RVM.labelOccupation` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direct_source_relative_budget` and `OAI.RVM.Admissible.source_majorant_relative_budget` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/RelativeClosedBinHitGeometry.lean (declaration OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude)

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.relative_closed_bin_cell_crude {s : Solution}
    {T M A P L lo hi a b c d massScale φ σ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (t₀ : ℝ) (ht₀ : t₀∈Icc c d) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (helo : σ^2/2 ≤ B.emin) (hehi : B.emax ≤ 8*σ^2)
    (hq : 4 ≤ σ*B.qmin) (hw : 4 ≤ σ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ENNReal.ofReal (40*B.rmax*(1+φ/σ)) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  sorry

end RVM

end

end OAI
end
