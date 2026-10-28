-- Prove2me | Theorems.Thm_OAI_RVM_Admissible_uniform_physical_population_increment
-- name    : OAI.RVM.Admissible.uniform_physical_population_increment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:13:51.264897+00:00
-- url     : https://prove2.me/theorems/9c288548-ede7-4db8-90a8-8478cbf66cb6
-- title:
--   OAI.RVM.Admissible.uniform_physical_population_increment: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.Admissible.uniform_physical_population_increment` of [lean/OAI/Analysis/VlasovMaxwell/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma Admissible.uniform_physical_population_increment {d : Datum} (hd : Admissible d)
--       (H : ℝ) :
--       ∃ M A P₀ : ℝ, 0 < M ∧ 0 < A ∧
--         ∀ U : ℝ, 0 < U → U ≤ H → ∀ s : Solution,
--         BoundedClassicalPrefix d s U → ∀ F : PhaseFlowOn s.E s.B U,
--           PopulationIncrement (fun z t => (F.flow z t).2) (tsupport d.f₀) U M A P₀
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.BoundedClassicalPrefix`, `OAI.RVM.PhaseFlowOn` and `OAI.RVM.PopulationIncrement` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.global_classical_solution` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Main.lean (declaration OAI.RVM.Admissible.uniform_physical_population_increment)

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
open scoped Topology ContDiff

namespace RVM

lemma Admissible.uniform_physical_population_increment {d : Datum} (hd : Admissible d)
    (H : ℝ) :
    ∃ M A P₀ : ℝ, 0 < M ∧ 0 < A ∧
      ∀ U : ℝ, 0 < U → U ≤ H → ∀ s : Solution,
      BoundedClassicalPrefix d s U → ∀ F : PhaseFlowOn s.E s.B U,
        PopulationIncrement (fun z t => (F.flow z t).2) (tsupport d.f₀) U M A P₀ := by
  sorry

end RVM

end

end OAI
end
