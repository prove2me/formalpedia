-- Prove2me | Theorems.Thm_OAI_Kadison_LittleGrothendieck_unitary_norm_le_one
-- name    : OAI.Kadison.LittleGrothendieck.unitary_norm_le_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:28.703693+00:00
-- url     : https://prove2.me/theorems/cf37e203-2240-4fec-b0ae-10775b22b3cc
-- title:
--   OAI.Kadison.LittleGrothendieck.unitary_norm_le_one: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.LittleGrothendieck`, with `open scoped Topology InnerProductSpace BoundedContinuousFunction`, `open Filter Set UniformSpace Completion`):
--
--   ```lean
--   lemma unitary_norm_le_one (u : unitary A) : ‖(u:A)‖≤1
--   ```
--
--   **Used by.** The proofs of `OAI.Kadison.ColumnModule.hom_column_sq` and `OAI.Kadison.MatrixTower.square_symmetry_after_average` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter Set UniformSpace Completion

namespace Kadison.LittleGrothendieck

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma unitary_norm_le_one (u : unitary A) : ‖(u:A)‖≤1 := by
  sorry

end Kadison.LittleGrothendieck

end

end
end

end OAI
end
