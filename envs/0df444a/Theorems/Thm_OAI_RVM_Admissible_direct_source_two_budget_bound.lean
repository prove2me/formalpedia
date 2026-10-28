-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direct_source_two_budget_bound
-- name    : OAI.RVM.Admissible.direct_source_two_budget_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:05:42.943413+00:00
-- url     : https://prove2.me/theorems/21eca09a-64d0-4f07-b915-ca54273110b9
-- title:
--   OAI.RVM.Admissible.direct_source_two_budget_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direct_source_two_budget_bound` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalDirectTransportDensity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalDirectTransportDensity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direct_source_two_budget_bound {d : Datum} (hd₀ : Admissible d) :
--       ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
--       ∀ (zX : Phase) (B : ClosedConeBin) (S : Set Phase)
--         (a b I p P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
--         tsupport (fun z=>s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
--         0<I → 0<p → 0<P → 0<θ → 0<φ → 0≤σ → 0<B.rmin → 0<B.Dmin →
--         p≤B.qmin → B.qmax≤P → θ^2/2≤B.dmin → B.dmax≤8*θ^2 →
--         φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.emax≤8*σ^2 →
--         (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let M := coneOccupation F.flow zX T s.f
--           (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
--             ENNReal.ofReal (B.rmin^2*B.Dmin)
--         let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
--         let Dg := ENNReal.ofReal (128*Cg*P^3*(min θ σ)^2)
--         let Db := ENNReal.ofReal (128*Cb*P^3*(min θ σ)^2)
--         (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
--           ENNReal.ofReal (80*φ/(p*θ^2))*
--             ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
--               (min (Dg^2*H) (Dg*M))^(1/2:ℝ))+
--           ENNReal.ofReal (80/p)*
--             ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
--               (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
--               (min (Db^2*H) (Db*M))^(1/2:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.DyadicWindow`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.closedBinEulerian`, `OAI.RVM.coneOccupation`, `OAI.RVM.goodFieldBudget`, `OAI.RVM.magneticFieldBudget`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalDirectSourceDensity` and `OAI.RVM.prefixFlow` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direct_remaining_source_deficit_short_uniform_expanded`, `OAI.RVM.Admissible.direct_source_deficit_short_sum`, `OAI.RVM.Admissible.direct_source_large_radius`, `OAI.RVM.Admissible.direct_source_relative_budget` and `OAI.RVM.Admissible.direct_source_small_deficit_short_sum` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalDirectTransportDensity.lean (declaration OAI.RVM.Admissible.direct_source_two_budget_bound)

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

lemma Admissible.direct_source_two_budget_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (B : ClosedConeBin) (S : Set Phase)
      (a b I p P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z=>s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<p → 0<P → 0<θ → 0<φ → 0≤σ → 0<B.rmin → 0<B.Dmin →
      p≤B.qmin → B.qmax≤P → θ^2/2≤B.dmin → B.dmax≤8*θ^2 →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.emax≤8*σ^2 →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
          ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*P^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*P^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/(p*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*M))^(1/2:ℝ))+
        ENNReal.ofReal (80/p)*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*M))^(1/2:ℝ)) := by
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

end

end OAI
end
