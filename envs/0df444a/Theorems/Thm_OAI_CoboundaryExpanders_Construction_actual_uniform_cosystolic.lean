-- Prove2me | Theorems.Thm_OAI_CoboundaryExpanders_Construction_actual_uniform_cosystolic
-- name    : OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:29:05.625597+00:00
-- url     : https://prove2.me/theorems/366dc91a-e6a7-4113-bb8c-ebdd215c5e97
-- title:
--   OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic: intermediate lemma from OpenAI, Bounded-degree coboundary expanders in every dimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoboundaryExpanders.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Bounded-degree coboundary expanders in every dimension*, OpenAI Math Release, September 24, 2026, result family 177, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic` of [lean/OAI/Combinatorics/Coboundary/Coboundary/Skeleton.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Coboundary/Coboundary/Skeleton.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoboundaryExpanders.Construction`, with `open InfiniteChains.FiniteWeights`):
--
--   ```lean
--   theorem actual_uniform_cosystolic (n : ℕ) (hn : 2 ≤ n) :
--       ∃ Q : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p → UniformCosystolic p n (by omega)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoboundaryExpanders.Construction.UniformCosystolic` (definitions bundle `OAIQ3Cb000` of this split).
--
--   **Used by.** The proof of `OAI.CoboundaryExpanders.main` of this split imports it.
-- source:
--   OpenAI, Bounded-degree coboundary expanders in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 177; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Coboundary/Coboundary/Skeleton.lean (declaration OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic)

import Mathlib
import Definitions.Def_OAIQ3Cb000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoboundaryExpanders.Construction
open InfiniteChains.FiniteWeights

theorem actual_uniform_cosystolic (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p → UniformCosystolic p n (by omega) := by
  sorry
end CoboundaryExpanders.Construction

end

end OAI
end
