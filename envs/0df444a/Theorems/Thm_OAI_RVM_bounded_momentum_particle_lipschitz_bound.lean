-- Prove2me | Theorems.Thm_OAI_RVM_bounded_momentum_particle_lipschitz_bound
-- name    : OAI.RVM.bounded_momentum_particle_lipschitz_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:22:11.251671+00:00
-- url     : https://prove2.me/theorems/11676a05-98d1-40d7-a98d-6cd7d7752c1c
-- title:
--   OAI.RVM.bounded_momentum_particle_lipschitz_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.bounded_momentum_particle_lipschitz_bound` of [lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma bounded_momentum_particle_lipschitz_bound {d : Datum} (hd : Admissible d) (P H : ℝ) (hH : 0≤H) :
--       ∃ C : ℝ, 0≤C ∧ ∀ (U : ℝ), 0<U → U≤H → ∀ (s : Solution),
--         BoundedClassicalPrefix d s U →
--         (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
--         ∀ t∈Icc (0:ℝ) U, ∀ z w : Phase, |s.f (t,z)-s.f (t,w)|≤C*‖z-w‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.BoundedClassicalPrefix` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.bounded_momentum_second_jet_bound` and `OAI.RVM.bounded_momentum_uniform_restart` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Continuation/GlobalContinuation.lean (declaration OAI.RVM.bounded_momentum_particle_lipschitz_bound)

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

lemma bounded_momentum_particle_lipschitz_bound {d : Datum} (hd : Admissible d) (P H : ℝ) (hH : 0≤H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (U : ℝ), 0<U → U≤H → ∀ (s : Solution),
      BoundedClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∀ t∈Icc (0:ℝ) U, ∀ z w : Phase, |s.f (t,z)-s.f (t,w)|≤C*‖z-w‖ := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
