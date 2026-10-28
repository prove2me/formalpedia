-- Prove2me | Theorems.Thm_OAI_RVM_prefix_spatial_gradient_volterra
-- name    : OAI.RVM.prefix_spatial_gradient_volterra
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:28:36.731708+00:00
-- url     : https://prove2.me/theorems/243049a6-435c-4238-bf9c-f1e8c670be47
-- title:
--   OAI.RVM.prefix_spatial_gradient_volterra: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.prefix_spatial_gradient_volterra` of [lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma prefix_spatial_gradient_volterra {d : Datum} (hd : Admissible d)
--       (P A M H : ℝ) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
--       ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
--       ∀ (s : Solution) (U : ℝ), BoundedClassicalPrefix d s U → 0<U → U≤H →
--         (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
--         (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
--         ∀ g : ℝ → ℝ, Continuous g →
--         (∀ u∈Icc (0:ℝ) U, ∀ y,
--           ‖fderiv ℝ (fun z => s.E (u,z)) y‖+‖fderiv ℝ (fun z => s.B (u,z)) y‖≤g u) →
--         ∀ t∈Icc (0:ℝ) U, ∀ x,
--           ‖fderiv ℝ (fun z => s.E (t,z)) x‖+‖fderiv ℝ (fun z => s.B (t,z)) x‖≤
--             B+K*(∫ u in Icc (0:ℝ) t,1+g u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.BoundedClassicalPrefix` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.bounded_momentum_field_gradient_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean (declaration OAI.RVM.prefix_spatial_gradient_volterra)

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

lemma prefix_spatial_gradient_volterra {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
    ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
    ∀ (s : Solution) (U : ℝ), BoundedClassicalPrefix d s U → 0<U → U≤H →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      ∀ g : ℝ → ℝ, Continuous g →
      (∀ u∈Icc (0:ℝ) U, ∀ y,
        ‖fderiv ℝ (fun z => s.E (u,z)) y‖+‖fderiv ℝ (fun z => s.B (u,z)) y‖≤g u) →
      ∀ t∈Icc (0:ℝ) U, ∀ x,
        ‖fderiv ℝ (fun z => s.E (t,z)) x‖+‖fderiv ℝ (fun z => s.B (t,z)) x‖≤
          B+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
