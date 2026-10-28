-- Prove2me | Theorems.Thm_OAI_RVM_exists_local_spatially_smooth_bounded_classical
-- name    : OAI.RVM.exists_local_spatially_smooth_bounded_classical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:24:26.872112+00:00
-- url     : https://prove2.me/theorems/7035fa5d-6246-40a3-96ac-b7ecad0dc699
-- title:
--   OAI.RVM.exists_local_spatially_smooth_bounded_classical: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.exists_local_spatially_smooth_bounded_classical` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/StrongLocalExistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/StrongLocalExistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem exists_local_spatially_smooth_bounded_classical (d : Datum) (hd : Admissible d) :
--       ∃ T : ℝ, 0<T ∧ ∃ s : Solution, C1ClassicalPrefix d s T ∧ SlabEquations s T ∧
--         BoundedSpatiallySmoothSlab T s.f ∧ BoundedSpatiallySmoothSlab T s.E ∧ BoundedSpatiallySmoothSlab T s.B
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.BoundedSpatiallySmoothSlab`, `OAI.RVM.C1ClassicalPrefix` and `OAI.RVM.SlabEquations` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.global_classical_of_uniform_prefix_momentum` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/StrongLocalExistence.lean (declaration OAI.RVM.exists_local_spatially_smooth_bounded_classical)

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

theorem exists_local_spatially_smooth_bounded_classical (d : Datum) (hd : Admissible d) :
    ∃ T : ℝ, 0<T ∧ ∃ s : Solution, C1ClassicalPrefix d s T ∧ SlabEquations s T ∧
      BoundedSpatiallySmoothSlab T s.f ∧ BoundedSpatiallySmoothSlab T s.E ∧ BoundedSpatiallySmoothSlab T s.B := by
  sorry

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end
