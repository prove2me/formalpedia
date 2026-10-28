-- Prove2me | Theorems.Thm_OAI_Kadison_InfiniteAmplification_separable_space
-- name    : OAI.Kadison.InfiniteAmplification.separable_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:35:59.491327+00:00
-- url     : https://prove2.me/theorems/88f00de6-bfaf-493f-9e6c-d12d827ebbe4
-- title:
--   OAI.Kadison.InfiniteAmplification.separable_space: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.InfiniteAmplification`, with `open scoped InnerProductSpace Topology`):
--
--   ```lean
--   theorem separable_space : TopologicalSpace.SeparableSpace (Space ι H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.InfiniteAmplification.Space` (definitions bundle `OAIQ039C006` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.CentralSpectral.exists_stable_center_spectral_model`, `OAI.Kadison.CentralSpectral.separable_uniform_bound` and `OAI.Kadison.CentralSpectral.stable_model_bound` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

namespace Kadison.InfiniteAmplification

variable {ι H : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem separable_space : TopologicalSpace.SeparableSpace (Space ι H) := by
  sorry

end Kadison.InfiniteAmplification

end

end
end

end OAI
end
