-- Prove2me | Theorems.Thm_OAI_Kadison_unitary_dihedral
-- name    : OAI.Kadison.unitary_dihedral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:31:49.03923+00:00
-- url     : https://prove2.me/theorems/007e40ee-d666-48b3-a835-73570d897b92
-- title:
--   OAI.Kadison.unitary_dihedral: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma unitary_dihedral {d s : unitary A} (hd : (d:A)*(d:A)=1) (hs : (s:A)*(s:A)=1) :
--       MulAut.conj d (d*s)=(d*s)⁻¹
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` of this split imports it.
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

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

include hp

omit hp in
lemma unitary_dihedral {d s : unitary A} (hd : (d:A)*(d:A)=1) (hs : (s:A)*(s:A)=1) :
    MulAut.conj d (d*s)=(d*s)⁻¹ := by
  sorry

end Kadison

end

end
end

end OAI
end
