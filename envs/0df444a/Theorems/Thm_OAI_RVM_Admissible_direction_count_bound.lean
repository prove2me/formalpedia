-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_direction_count_bound
-- name    : OAI.RVM.Admissible.direction_count_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:06:42.854468+00:00
-- url     : https://prove2.me/theorems/bebb8104-01d1-4626-a79a-cebad0f22187
-- title:
--   OAI.RVM.Admissible.direction_count_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.direction_count_bound` of [lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.direction_count_bound {d : Datum} (hd : Admissible d)
--       (T₀ M A : ℝ) (hM : 0<M) (hA : 0≤A) :
--       ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (zX : Phase) (S : Set Phase) (a b w δ : ℝ),
--         zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
--         0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
--         P^(3/5:ℝ)≤w → w≤P → w^(-3/5:ℝ)≤δ → δ≤1 →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
--         (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
--         (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
--         IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
--         (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--       ∀ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
--           (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b w δ,
--         (D.count:ℝ)≤C*(Real.log (2+P))^6/δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix` and `OAI.RVM.WeightedDirectionPartition` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.cross`, `OAI.RVM.q` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI_RVM_Admissible_direction_closedEulerian_improved` and `OAI.RVM.Admissible.exists_bounded_direction_partition` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/DirectionCounts.lean (declaration OAI.RVM.Admissible.direction_count_bound)

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

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

lemma Admissible.direction_count_bound {d : Datum} (hd : Admissible d)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0≤A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (S : Set Phase) (a b w δ : ℝ),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      P^(3/5:ℝ)≤w → w≤P → w^(-3/5:ℝ)≤δ → δ≤1 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
        (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b w δ,
      (D.count:ℝ)≤C*(Real.log (2+P))^6/δ := by
  sorry

end RVM

end

end OAI
end
