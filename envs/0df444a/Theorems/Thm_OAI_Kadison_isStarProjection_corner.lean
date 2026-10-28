-- Prove2me | Theorems.Thm_OAI_Kadison_isStarProjection_corner
-- name    : OAI.Kadison.isStarProjection_corner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:05.086998+00:00
-- url     : https://prove2.me/theorems/a65e3150-53ba-40bb-b214-d125a5749d51
-- title:
--   OAI.Kadison.isStarProjection_corner: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma isStarProjection_corner {e : Corner hp} (he : IsStarProjection (e:A)) :
--       IsStarProjection e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Corner`, `OAI.Kadison.cornerSubalgebra`, `OAI.Kadison.instRingCorner` and `OAI.Kadison.instStarRingCorner` (definitions bundle `OAIQ039C004` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C004

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

include hp

lemma isStarProjection_corner {e : Corner hp} (he : IsStarProjection (e:A)) :
    IsStarProjection e := by
  sorry

end Kadison

end

end
end

end OAI
end
