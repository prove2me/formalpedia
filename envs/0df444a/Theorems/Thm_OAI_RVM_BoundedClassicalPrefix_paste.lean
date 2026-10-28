-- Prove2me | Theorems.Thm_OAI_RVM_BoundedClassicalPrefix_paste
-- name    : OAI.RVM.BoundedClassicalPrefix.paste
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:14:31.309817+00:00
-- url     : https://prove2.me/theorems/3331cf9e-e73f-4427-bb2a-b3b61c596b82
-- title:
--   OAI.RVM.BoundedClassicalPrefix.paste: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.BoundedClassicalPrefix.paste` of [lean/OAI/Analysis/VlasovMaxwell/Regularity/SlabEvolutionRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/SlabEvolutionRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma BoundedClassicalPrefix.paste {d : Datum} {s a : Solution} {T S : ℝ}
--       (hT : 0<T) (hS : 0<S) (hs : BoundedClassicalPrefix d s T)
--       (ha : BoundedClassicalPrefix (timeSliceDatum s T) a S) :
--       BoundedClassicalPrefix d (pasteSolution T s a) (T+S)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.BoundedClassicalPrefix`, `OAI.RVM.pasteSolution` and `OAI.RVM.timeSliceDatum` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum` and `OAI.RVM.Solution` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.bounded_momentum_uniform_restart` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/SlabEvolutionRegularity.lean (declaration OAI.RVM.BoundedClassicalPrefix.paste)

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

lemma BoundedClassicalPrefix.paste {d : Datum} {s a : Solution} {T S : ℝ}
    (hT : 0<T) (hS : 0<S) (hs : BoundedClassicalPrefix d s T)
    (ha : BoundedClassicalPrefix (timeSliceDatum s T) a S) :
    BoundedClassicalPrefix d (pasteSolution T s a) (T+S) := by
  sorry

end RVM

end

end OAI
end
