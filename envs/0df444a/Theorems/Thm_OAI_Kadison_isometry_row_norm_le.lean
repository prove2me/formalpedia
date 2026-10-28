-- Prove2me | Theorems.Thm_OAI_Kadison_isometry_row_norm_le
-- name    : OAI.Kadison.isometry_row_norm_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:13:12.052495+00:00
-- url     : https://prove2.me/theorems/fb876a01-25df-473a-a911-17af084b0ff0
-- title:
--   OAI.Kadison.isometry_row_norm_le: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped InnerProductSpace BigOperators`):
--
--   ```lean
--   lemma isometry_row_norm_le : ‖operatorRow h (fun i => (v i : K →L[ℂ] K))‖≤1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.operatorRow` (definitions bundle `OAIQ039C019` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.uniform_commutator_of_isometries` of this split imports it.
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

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

section Isometries

variable (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
  (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0)

include hv in
lemma isometry_row_norm_le : ‖operatorRow h (fun i => (v i : K →L[ℂ] K))‖≤1 := by
  sorry

end Isometries

end Kadison

end

end
end

end OAI
end
