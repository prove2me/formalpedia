-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_projected_source_structural_edge_log_sum
-- name    : OAI.RVM.Admissible.projected_source_structural_edge_log_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:09:55.074966+00:00
-- url     : https://prove2.me/theorems/7d402265-385a-4b67-b62d-1a3952db425e
-- title:
--   OAI.RVM.Admissible.projected_source_structural_edge_log_sum: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.projected_source_structural_edge_log_sum` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCutoffs.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCutoffs.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.projected_source_structural_edge_log_sum {d : Datum} (hd₀ : Admissible d) :
--       ∃C : ℝ,0≤ C ∧
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤ T → (∀z,s.f (0,z)=d.f₀ z) →
--       ∀ (zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w M A P : ℝ),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
--         0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 0< w → w≤ P →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
--         (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let X := fun t=>(prefixFlow F.flow T zX t).1
--         let V := fun t=>(prefixFlow F.flow T zX t).2
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         let edge : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∧
--           cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16}
--         (∑'k : Fin 4→ℕ,edge.indicator (fun k=>∫⁻z : ConeCoordinate,
--             physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
--               ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
--         ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.cappedRepresentative`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalProjectedSourceDensity`, `OAI.RVM.prefixFlow`, `OAI.RVM.representativeClosedBin` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCutoffs.lean (declaration OAI.RVM.Admissible.projected_source_structural_edge_log_sum)

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

lemma Admissible.projected_source_structural_edge_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤ C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
      0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 0< w → w≤ P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let edge : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∧
        cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16}
      (∑'k : Fin 4→ℕ,edge.indicator (fun k=>∫⁻z : ConeCoordinate,
          physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
            ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
