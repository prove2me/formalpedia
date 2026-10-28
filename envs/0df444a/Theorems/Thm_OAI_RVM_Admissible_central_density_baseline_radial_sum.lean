-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_central_density_baseline_radial_sum
-- name    : OAI.RVM.Admissible.central_density_baseline_radial_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:00:06.012295+00:00
-- url     : https://prove2.me/theorems/83edfdab-11fc-4bd7-937e-00dbd75fe17d
-- title:
--   OAI.RVM.Admissible.central_density_baseline_radial_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.central_density_baseline_radial_sum` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/ProjectedSourceStableFarBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ProjectedSourceStableFarBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.central_density_baseline_radial_sum {d : Datum} (hd₀ : Admissible d) :
--       ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
--         ∀(zX : Phase) (S : Set Phase) (np nθ nφ : ℕ)
--           (a b I len w M A P L massScale Cs : ℝ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
--         0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
--         massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
--         cappedRepresentative nθ ≤ cappedRepresentative nφ/16 →
--         32 ≤ cappedRepresentative nφ*w →
--         2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative nφ+
--           Real.sqrt (A*L/cappedRepresentative nφ)))⁻¹^2 →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
--         let p := sourceRepresentative np
--         let φ := cappedRepresentative nφ
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         (∑'nr : ℕ,ENNReal.ofReal (78400000*(cappedRepresentative nφ)^2/cappedRepresentative nθ)*
--           (∫⁻z : ConeCoordinate,physicalBinDensity s X V (B nr) z.1 z.2.1 z.2.2
--             ∂physicalBinMeasure V (B nr) (Icc a b))) ≤
--         ENNReal.ofReal (C*(1+E)*(6*Real.sqrt I*Real.sqrt (1+I/len)*p*φ^2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.physicalBinDensity`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.prefixFlow`, `OAI.RVM.representativeClosedBin`, `OAI.RVM.sourceRepresentative` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.central_density_small_sector_log_sum` and `OAI.RVM.Admissible.direct_transport_sharp_all_radii` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ProjectedSourceStableFarBound.lean (declaration OAI.RVM.Admissible.central_density_baseline_radial_sum)

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

lemma Admissible.central_density_baseline_radial_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (np nθ nφ : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
      cappedRepresentative nθ ≤ cappedRepresentative nφ/16 →
      32 ≤ cappedRepresentative nφ*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative nφ+
        Real.sqrt (A*L/cappedRepresentative nφ)))⁻¹^2 →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nφ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,ENNReal.ofReal (78400000*(cappedRepresentative nφ)^2/cappedRepresentative nθ)*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (B nr) z.1 z.2.1 z.2.2
          ∂physicalBinMeasure V (B nr) (Icc a b))) ≤
      ENNReal.ofReal (C*(1+E)*(6*Real.sqrt I*Real.sqrt (1+I/len)*p*φ^2)) := by
  sorry

end RVM

end

end OAI
end
