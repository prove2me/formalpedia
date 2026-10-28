-- Prove2me | Theorems.Thm_OAI_Kadison_projectionSymmetry_right
-- name    : OAI.Kadison.projectionSymmetry_right
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:17:47.427993+00:00
-- url     : https://prove2.me/theorems/b4467f4d-93e2-4b4b-abe5-5892512b7062
-- title:
--   OAI.Kadison.projectionSymmetry_right: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma projectionSymmetry_right : (projectionSymmetry hp:A)*p=p
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.projectionSymmetry` (definitions bundle `OAIQ039C019` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C019

section

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

lemma projectionSymmetry_right : (projectionSymmetry hp:A)*p=p := by
  sorry

end Kadison

end

end
end

end OAI
end
