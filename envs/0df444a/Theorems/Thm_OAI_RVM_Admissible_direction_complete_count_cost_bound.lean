-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direction_complete_count_cost_bound
-- name    : OAI.RVM.Admissible.direction_complete_count_cost_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:06:46.38363+00:00
-- url     : https://prove2.me/theorems/c5038e9f-a04f-4409-9714-360ffcee3f77
-- title:
--   OAI.RVM.Admissible.direction_complete_count_cost_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direction_complete_count_cost_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direction_complete_count_cost_bound {d : Datum} (hd₀ : Admissible d)
--       (T₀ : ℝ) :
--       ∃ Ct Cr Cf Cl Cg Ci Ck Cw Cb : ℝ,
--         0≤Ct ∧ 0≤Cr ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ci ∧ 0≤Ck ∧ 0≤Cw ∧ 0≤Cb ∧
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (S : Set Phase) (a b w M A P δ : ℝ) (_ : 0<w),
--         zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
--         0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
--         0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
--         (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
--         (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--       ∀ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
--           (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b w δ,
--         ENNReal.ofReal ((D.count-1:ℕ)*w*δ/2)≤
--         ENNReal.ofReal (4*Real.pi)⁻¹ *
--          (directionUnionBudget (∫x : Vec,totalEnergy s (0,x)) T w M A P Ct Cr Cf Cl Cg+
--           ENNReal.ofReal (Ci*T*(b-a))+
--           (D.count-1:ℕ)*ENNReal.ofReal (2*Cw*Real.sqrt (max 1 T)*(Real.log (2+P))^2)+
--           (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
--             ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w))+
--         ENNReal.ofReal (Cb*(b-a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.WeightedDirectionPartition`, `OAI.RVM.directionUnionBudget`, `OAI.RVM.prefixMomentumForce` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.cross`, `OAI.RVM.q` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_count_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean (declaration OAI.RVM.Admissible.direction_complete_count_cost_bound)

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

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

lemma Admissible.direction_complete_count_cost_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃ Ct Cr Cf Cl Cg Ci Ck Cw Cb : ℝ,
      0≤Ct ∧ 0≤Cr ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ci ∧ 0≤Ck ∧ 0≤Cw ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P δ : ℝ) (_ : 0<w),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
        (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b w δ,
      ENNReal.ofReal ((D.count-1:ℕ)*w*δ/2)≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
       (directionUnionBudget (∫x : Vec,totalEnergy s (0,x)) T w M A P Ct Cr Cf Cl Cg+
        ENNReal.ofReal (Ci*T*(b-a))+
        (D.count-1:ℕ)*ENNReal.ofReal (2*Cw*Real.sqrt (max 1 T)*(Real.log (2+P))^2)+
        (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
          ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w))+
      ENNReal.ofReal (Cb*(b-a)) := by
  sorry

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end RVM

end

end OAI
end
