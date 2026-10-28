-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direction_sourceCutoff_label_log_bound
-- name    : OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:31.762827+00:00
-- url     : https://prove2.me/theorems/21b3d964-79c2-4839-916c-9d6b299781f7
-- title:
--   OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCutoffs.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCutoffs.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direction_sourceCutoff_label_log_bound {d : Datum} (hd₀ : Admissible d)
--       (T₀ : ℝ) :
--       ∃Ce Cf Cl : ℝ,0≤ Ce ∧ 0≤ Cf ∧ 0≤ Cl ∧
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤ T → T≤ T₀ → (∀z,s.f (0,z)=d.f₀ z) →
--       ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
--         0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 1≤ w → w≤ P → P≤ w^2 →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
--         (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
--         (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)
--           (labelReceiverTime F.flow zX T p)
--           (partialCutoffLabelCost s F.flow zX T (directionSelection T)
--             (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)≤
--         ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
--         ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
--         ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.cutoffSourceTangent`, `OAI.RVM.directionSelection`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.lorentzField`, `OAI.RVM.partialCutoffLabelCost`, `OAI.RVM.prefixAngularMultiplier` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_selected_bulk_log_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCutoffs.lean (declaration OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound)

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

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direction_sourceCutoff_label_log_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ce Cf Cl : ℝ,0≤ Ce ∧ 0≤ Cf ∧ 0≤ Cl ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → T≤ T₀ → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
      0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 1≤ w → w≤ P → P≤ w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T (directionSelection T)
          (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)≤
      ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2) := by
  sorry

end RVM

end

end OAI
end
