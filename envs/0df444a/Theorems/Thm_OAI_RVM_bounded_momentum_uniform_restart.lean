-- Prove2me | Theorems.Thm_OAI_RVM_bounded_momentum_uniform_restart
-- name    : OAI.RVM.bounded_momentum_uniform_restart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:22:43.216783+00:00
-- url     : https://prove2.me/theorems/19018a97-471c-4f21-8dfe-856a07fb2135
-- title:
--   OAI.RVM.bounded_momentum_uniform_restart: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.bounded_momentum_uniform_restart` of [lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem bounded_momentum_uniform_restart {d : Datum} (hd : Admissible d)
--       (P H : ℝ) (hH : 0≤H) :
--       ∃ δ : ℝ, 0<δ ∧ ∀ U : ℝ, 0<U → U≤H → ∀ s : Solution,
--         BoundedClassicalPrefix d s U →
--         (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
--         ∃ a : Solution, BoundedClassicalPrefix d a (U+δ) ∧
--           ∀ t∈Icc (0:ℝ) U, (∀ z, a.f (t,z)=s.f (t,z)) ∧
--             (∀ x, a.E (t,x)=s.E (t,x)) ∧ (∀ x, a.B (t,x)=s.B (t,x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.BoundedClassicalPrefix` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.global_classical_of_uniform_prefix_momentum` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean (declaration OAI.RVM.bounded_momentum_uniform_restart)

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

theorem bounded_momentum_uniform_restart {d : Datum} (hd : Admissible d)
    (P H : ℝ) (hH : 0≤H) :
    ∃ δ : ℝ, 0<δ ∧ ∀ U : ℝ, 0<U → U≤H → ∀ s : Solution,
      BoundedClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∃ a : Solution, BoundedClassicalPrefix d a (U+δ) ∧
        ∀ t∈Icc (0:ℝ) U, (∀ z, a.f (t,z)=s.f (t,z)) ∧
          (∀ x, a.E (t,x)=s.E (t,x)) ∧ (∀ x, a.B (t,x)=s.B (t,x)) := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
