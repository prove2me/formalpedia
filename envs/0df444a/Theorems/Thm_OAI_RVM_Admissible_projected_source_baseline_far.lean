-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_projected_source_baseline_far
-- name    : OAI.RVM.Admissible.projected_source_baseline_far
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:09:30.095896+00:00
-- url     : https://prove2.me/theorems/fae93678-2a93-45f8-830d-8772793881ba
-- title:
--   OAI.RVM.Admissible.projected_source_baseline_far: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.projected_source_baseline_far` of [lean/OAI/Analysis/VlasovMaxwell/Population/CappedRepresentativePos.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/CappedRepresentativePos.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.projected_source_baseline_far {d : Datum} (hd₀ : Admissible d) :
--       ∃ Cg Cb c : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ 0 ≤ c ∧
--       ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
--         ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
--           (a b I len w M A P L massScale Cs : ℝ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
--         0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
--         massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
--         cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
--         32 ≤ cappedRepresentative (k 2)*w →
--         2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative (k 2)+
--           Real.sqrt (A*L/cappedRepresentative (k 2))))⁻¹^2 →
--         (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
--         let p := sourceRepresentative (k 0)
--         let θ := cappedRepresentative (k 1)
--         let φ := cappedRepresentative (k 2)
--         let r := max 1 T*cappedRepresentative (k 3)
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let B := representativeClosedBin T w k
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         let mass := ENNReal.ofReal (568197120*E*(1+I/len)/(p*r*φ^2))
--         (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
--           ∂physicalBinMeasure V B (Icc a b))  ≤
--         ENNReal.ofReal (128*(3840+94080000*c)*φ^2/(p*θ^2))*
--           ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
--             (ENNReal.ofReal (128*Cg*p^3*θ^2)*mass)^(1/2:ℝ))+
--         ENNReal.ofReal (128*(3840+94080000*c)*φ/p)*
--           ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*
--             (ENNReal.ofReal (128*Cb*p^3*θ^2)*mass)^(1/2:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalProjectedSourceDensity`, `OAI.RVM.prefixFlow`, `OAI.RVM.representativeClosedBin`, `OAI.RVM.sourceRepresentative` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.projected_source_stable_far_log_sum` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/CappedRepresentativePos.lean (declaration OAI.RVM.Admissible.projected_source_baseline_far)

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

lemma Admissible.projected_source_baseline_far {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb c : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ 0 ≤ c ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative (k 2)+
        Real.sqrt (A*L/cappedRepresentative (k 2))))⁻¹^2 →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      let mass := ENNReal.ofReal (568197120*E*(1+I/len)/(p*r*φ^2))
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b))  ≤
      ENNReal.ofReal (128*(3840+94080000*c)*φ^2/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (ENNReal.ofReal (128*Cg*p^3*θ^2)*mass)^(1/2:ℝ))+
      ENNReal.ofReal (128*(3840+94080000*c)*φ/p)*
        ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*
          (ENNReal.ofReal (128*Cb*p^3*θ^2)*mass)^(1/2:ℝ)) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end
