-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_source_majorant_relative_budget
-- name    : OAI.RVM.Admissible.source_majorant_relative_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:12:32.311697+00:00
-- url     : https://prove2.me/theorems/d67df217-869d-4c66-b69e-1142f2481d68
-- title:
--   OAI.RVM.Admissible.source_majorant_relative_budget: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.source_majorant_relative_budget` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceMajorant.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceMajorant.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.source_majorant_relative_budget {d : Datum} (hd₀ : Admissible d) :
--       ∃Cg Cb : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
--         ∀(zX : Phase) (B : ClosedConeBin) (S : Set Phase)
--           (M A P L a b massScale φ θ σ Cs p len I : ℝ) (k j : ℕ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0 ≤ a → b ≤ T → a ≤ b → 0 < p → 0 < len → len ≤ I → b-a ≤ I →
--         0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale →
--         0 < φ → 0 < θ → 0 < σ → σ ≤ 1 → 128 ≤ Cs →
--         2*len ≤ (Cs*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 →
--         p/128 ≤ B.qmin → B.qmax ≤ p/32 → massScale ≤ B.qmin → massScale ≤ B.wmin →
--         0 < B.rmin → 0 ≤ B.rmax → 0 < B.Dmin →
--         θ^2/2 ≤ B.dmin → B.dmax ≤ 8*θ^2 → φ^2/2 ≤ B.Dmin → B.Dmax ≤ 8*φ^2 →
--         σ^2/2 ≤ B.emin → B.emax ≤ 8*σ^2 → 4 ≤ σ*B.qmin → 4 ≤ σ*B.wmin →
--         (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         let O := (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
--           ENNReal.ofReal (B.rmin^2*B.Dmin)
--         let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
--         let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
--         let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
--         (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
--           ENNReal.ofReal (80*φ/((p/128)*θ^2))*
--             ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
--               (min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
--           ENNReal.ofReal (80/(p/128))*
--             ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
--               (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
--               (min (Db^2*H) (Db*O))^(1/2:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.DyadicWindow`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.goodFieldBudget`, `OAI.RVM.magneticFieldBudget`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalSourceMajorantDensity`, `OAI.RVM.prefixFlow` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.source_majorant_relative_short_radial_sum` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceMajorant.lean (declaration OAI.RVM.Admissible.source_majorant_relative_budget)

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

lemma Admissible.source_majorant_relative_budget {d : Datum} (hd₀ : Admissible d) :
    ∃Cg Cb : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (B : ClosedConeBin) (S : Set Phase)
        (M A P L a b massScale φ θ σ Cs p len I : ℝ) (k j : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < p → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale →
      0 < φ → 0 < θ → 0 < σ → σ ≤ 1 → 128 ≤ Cs →
      2*len ≤ (Cs*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 →
      p/128 ≤ B.qmin → B.qmax ≤ p/32 → massScale ≤ B.qmin → massScale ≤ B.wmin →
      0 < B.rmin → 0 ≤ B.rmax → 0 < B.Dmin →
      θ^2/2 ≤ B.dmin → B.dmax ≤ 8*θ^2 → φ^2/2 ≤ B.Dmin → B.Dmax ≤ 8*φ^2 →
      σ^2/2 ≤ B.emin → B.emax ≤ 8*σ^2 → 4 ≤ σ*B.qmin → 4 ≤ σ*B.wmin →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let O := (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
        ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/((p/128)*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
        ENNReal.ofReal (80/(p/128))*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
