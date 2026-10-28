-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_exists_stable_direction_partition
-- name    : OAI.RVM.Admissible.exists_stable_direction_partition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:56.669613+00:00
-- url     : https://prove2.me/theorems/3f630def-f015-482f-9db8-dddd316912ac
-- title:
--   OAI.RVM.Admissible.exists_stable_direction_partition: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.exists_stable_direction_partition` of [lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.exists_stable_direction_partition {d : Datum} (hd : Admissible d)
--       (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
--       ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
--       ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
--         SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
--       ∀ (z : Phase) (a b r m δ : ℝ),
--         z∈tsupport d.f₀ → 0≤a → b≤T → r∈Icc a b → 0 < m → m≤q (F.flow z r).2 →
--         b-a≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
--         b-a≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
--         (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
--         (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
--         ∃ k : ℕ, ∃ D : WeightedDirectionPartition (fun t=>(F.flow z t).2)
--           (fun t=>s.E (t,(F.flow z t).1)+cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) a b ((2:ℝ)^k) δ,
--           (D.count:ℝ)≤C*(Real.log (2+P))^6/δ ∧ 16≤(2:ℝ)^k ∧
--           (∀t∈Icc a b,m/2≤q (F.flow z t).2 ∧ (F.flow z t).2≠0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.IncrementBootstrap`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix` and `OAI.RVM.WeightedDirectionPartition` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.cross`, `OAI.RVM.q` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_stable_closed_cell_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Population/PartitionOccupation.lean (declaration OAI.RVM.Admissible.exists_stable_direction_partition)

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

lemma Admissible.exists_stable_direction_partition {d : Datum} (hd : Admissible d)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (z : Phase) (a b r m δ : ℝ),
      z∈tsupport d.f₀ → 0≤a → b≤T → r∈Icc a b → 0 < m → m≤q (F.flow z r).2 →
      b-a≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
      b-a≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ∃ k : ℕ, ∃ D : WeightedDirectionPartition (fun t=>(F.flow z t).2)
        (fun t=>s.E (t,(F.flow z t).1)+cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) a b ((2:ℝ)^k) δ,
        (D.count:ℝ)≤C*(Real.log (2+P))^6/δ ∧ 16≤(2:ℝ)^k ∧
        (∀t∈Icc a b,m/2≤q (F.flow z t).2 ∧ (F.flow z t).2≠0) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
