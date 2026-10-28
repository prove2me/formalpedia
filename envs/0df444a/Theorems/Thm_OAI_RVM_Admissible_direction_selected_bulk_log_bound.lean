-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direction_selected_bulk_log_bound
-- name    : OAI.RVM.Admissible.direction_selected_bulk_log_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:15.194998+00:00
-- url     : https://prove2.me/theorems/764b5762-1322-4193-9feb-3de5a357c067
-- title:
--   OAI.RVM.Admissible.direction_selected_bulk_log_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direction_selected_bulk_log_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direction_selected_bulk_log_bound {d : Datum} (hd₀ : Admissible d)
--       (T₀ : ℝ) :
--       ∃Ce Cf Cl Cg Ck : ℝ,0≤Ce ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ck ∧
--       ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         EnergyPrefix s T → 0≤T → T≤T₀ → (∀z,s.f (0,z)=d.f₀ z) →
--       ∀(zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
--         IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
--         0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
--         0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
--         (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
--         (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         let E := ∫x : Vec,totalEnergy s (0,x)
--         (∫⁻p : ℝ×Phase,selectedMultiplierBulkDensity s F.flow zX T (directionSelection T)
--           ((Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)) p)≤
--         ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
--         ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
--         ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2)+
--         ENNReal.ofReal (Cg*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)+
--         (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
--           ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.directionSelection`, `OAI.RVM.prefixAngularMultiplier`, `OAI.RVM.prefixMomentumForce`, `OAI.RVM.selectedMultiplierBulkDensity` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.q` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_physical_family_log_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/SelectedDirection.lean (declaration OAI.RVM.Admissible.direction_selected_bulk_log_bound)

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

lemma Admissible.direction_selected_bulk_log_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ce Cf Cl Cg Ck : ℝ,0≤Ce ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ck ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → T≤T₀ → (∀z,s.f (0,z)=d.f₀ z) →
    ∀(zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p : ℝ×Phase,selectedMultiplierBulkDensity s F.flow zX T (directionSelection T)
        ((Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)) p)≤
      ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2)+
      ENNReal.ofReal (Cg*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)+
      (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
