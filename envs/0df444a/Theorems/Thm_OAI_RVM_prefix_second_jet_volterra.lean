-- Prove2me | Theorems.Thm_OAI_RVM_prefix_second_jet_volterra
-- name    : OAI.RVM.prefix_second_jet_volterra
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:28:09.123798+00:00
-- url     : https://prove2.me/theorems/2f5c0114-efc3-402c-8eb2-f0eef18377cb
-- title:
--   OAI.RVM.prefix_second_jet_volterra: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.prefix_second_jet_volterra` of [lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma prefix_second_jet_volterra {d : Datum} (hd : Admissible d)
--       (P A L M N H : ℝ) (hL : 0≤L) (hM : 0≤M) (hN : 0≤N) (hH : 0≤H) :
--       ∃ D K : ℝ,0≤D ∧ 0≤K ∧ ∀ (s : Solution) (U : ℝ),
--         BoundedClassicalPrefix d s U → 0<U → U≤H →
--         (∀ u∈Icc (0:ℝ) U,∀ y v,|s.f (u,y,v)|≤A) →
--         (∀ u∈Icc (0:ℝ) U,∀ y v,P<‖v‖ → s.f (u,y,v)=0) →
--         (∀ u∈Icc (0:ℝ) U,∀ y,‖s.E (u,y)‖≤L ∧ ‖s.B (u,y)‖≤L) →
--         (∀ u∈Icc (0:ℝ) U,∀ z w : Phase,|s.f (u,z)-s.f (u,w)|≤M*‖z-w‖) →
--         SpatialFieldLip U N s.E s.B →
--         ∀ g : ℝ → ℝ,Continuous g →
--         (∀ u∈Icc (0:ℝ) U,∀ z,secondJetSum s u z≤g u) →
--         ∀ t∈Icc (0:ℝ) U,∀ z,secondJetSum s t z≤D+K*(∫ r in Icc (0:ℝ) t,1+g r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.BoundedClassicalPrefix`, `OAI.RVM.SpatialFieldLip` and `OAI.RVM.secondJetSum` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.bounded_momentum_second_jet_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean (declaration OAI.RVM.prefix_second_jet_volterra)

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
open scoped Topology ContDiff

namespace RVM

lemma prefix_second_jet_volterra {d : Datum} (hd : Admissible d)
    (P A L M N H : ℝ) (hL : 0≤L) (hM : 0≤M) (hN : 0≤N) (hH : 0≤H) :
    ∃ D K : ℝ,0≤D ∧ 0≤K ∧ ∀ (s : Solution) (U : ℝ),
      BoundedClassicalPrefix d s U → 0<U → U≤H →
      (∀ u∈Icc (0:ℝ) U,∀ y v,|s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U,∀ y v,P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U,∀ y,‖s.E (u,y)‖≤L ∧ ‖s.B (u,y)‖≤L) →
      (∀ u∈Icc (0:ℝ) U,∀ z w : Phase,|s.f (u,z)-s.f (u,w)|≤M*‖z-w‖) →
      SpatialFieldLip U N s.E s.B →
      ∀ g : ℝ → ℝ,Continuous g →
      (∀ u∈Icc (0:ℝ) U,∀ z,secondJetSum s u z≤g u) →
      ∀ t∈Icc (0:ℝ) U,∀ z,secondJetSum s t z≤D+K*(∫ r in Icc (0:ℝ) t,1+g r) := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
