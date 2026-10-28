-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_uniform_actual_magnetic_Cauchy
-- name    : OAI.RVM.Admissible.uniform_actual_magnetic_Cauchy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:13:46.77799+00:00
-- url     : https://prove2.me/theorems/c4f07b45-cfae-4435-8aaa-a8a83349538f
-- title:
--   OAI.RVM.Admissible.uniform_actual_magnetic_Cauchy: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.uniform_actual_magnetic_Cauchy` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.uniform_actual_magnetic_Cauchy {d : Datum} (hd₀ : Admissible d) :
--       ∃ C₀ : ℝ, 0≤C₀ ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤T → (∀ z,s.f (0,z)=d.f₀ z) → ∀ (zX : Phase) (C : ClosedConeBin) (S : Set Phase)
--         (a b I P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
--         tsupport (fun z => s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
--         0<I → 0<P → 0≤θ → 0≤φ → 0≤σ → 0<C.rmin → 0<C.Dmin → φ^2/2≤C.Dmin →
--         C.qmax≤P → C.dmax≤8*θ^2 → C.Dmax≤8*φ^2 → C.emax≤8*σ^2 →
--         (∀ D∈Icc C.Dmin C.Dmax, DyadicWindow k j (Real.sqrt (D/2))) →
--         let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
--         let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
--         let N : ConeCoordinate → ℝ≥0∞ := fun z => physicalBinDensity s X V C z.1 z.2.1 z.2.2
--         let D := ENNReal.ofReal (128*C₀*P^3*(min θ σ)^2)
--         let M := coneOccupation F.flow zX T s.f
--           (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) /
--             ENNReal.ofReal (C.rmin^2*C.Dmin)
--         (∫⁻ z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1) * ENNReal.ofReal φ *
--           ENNReal.ofReal (prefixConeMagnetic s T X z) * N z ∂physicalBinMeasure V C (Icc a b)) ≤
--         (ENNReal.ofReal (2*I) * magneticFieldBudget s F.flow zX T k
--             (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j)^(1/2:ℝ) *
--           (min (D^2*(volume (Icc a b)*ENNReal.ofReal (C.rmax-C.rmin)*ENNReal.ofReal (384*φ^2)))
--             (D*M))^(1/2:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.DyadicWindow`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.closedBinEulerian`, `OAI.RVM.coneOccupation`, `OAI.RVM.magneticFieldBudget`, `OAI.RVM.physicalBinDensity`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.prefixConeMagnetic` and `OAI.RVM.prefixFlow` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direct_source_two_budget_bound`, `OAI.RVM.Admissible.magnetic_low_uniform`, `OAI.RVM.Admissible.projected_source_two_budget_bound`, `OAI.RVM.Admissible.representative_magnetic_large` and `OAI.RVM.Admissible.source_majorant_two_budget_bound` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean (declaration OAI.RVM.Admissible.uniform_actual_magnetic_Cauchy)

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

lemma Admissible.uniform_actual_magnetic_Cauchy {d : Datum} (hd₀ : Admissible d) :
    ∃ C₀ : ℝ, 0≤C₀ ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀ z,s.f (0,z)=d.f₀ z) → ∀ (zX : Phase) (C : ClosedConeBin) (S : Set Phase)
      (a b I P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z => s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<P → 0≤θ → 0≤φ → 0≤σ → 0<C.rmin → 0<C.Dmin → φ^2/2≤C.Dmin →
      C.qmax≤P → C.dmax≤8*θ^2 → C.Dmax≤8*φ^2 → C.emax≤8*σ^2 →
      (∀ D∈Icc C.Dmin C.Dmax, DyadicWindow k j (Real.sqrt (D/2))) →
      let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
      let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
      let N : ConeCoordinate → ℝ≥0∞ := fun z => physicalBinDensity s X V C z.1 z.2.1 z.2.2
      let D := ENNReal.ofReal (128*C₀*P^3*(min θ σ)^2)
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) /
          ENNReal.ofReal (C.rmin^2*C.Dmin)
      (∫⁻ z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1) * ENNReal.ofReal φ *
        ENNReal.ofReal (prefixConeMagnetic s T X z) * N z ∂physicalBinMeasure V C (Icc a b)) ≤
      (ENNReal.ofReal (2*I) * magneticFieldBudget s F.flow zX T k
          (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j)^(1/2:ℝ) *
        (min (D^2*(volume (Icc a b)*ENNReal.ofReal (C.rmax-C.rmin)*ENNReal.ofReal (384*φ^2)))
          (D*M))^(1/2:ℝ) := by
  sorry

end RVM

end

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

end

end OAI
end
