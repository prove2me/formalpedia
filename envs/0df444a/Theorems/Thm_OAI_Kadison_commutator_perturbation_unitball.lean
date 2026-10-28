-- Prove2me | Theorems.Thm_OAI_Kadison_commutator_perturbation_unitball
-- name    : OAI.Kadison.commutator_perturbation_unitball
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:31:00.134089+00:00
-- url     : https://prove2.me/theorems/c79ace7e-8ca1-4485-b8ff-b046e39bcd88
-- title:
--   OAI.Kadison.commutator_perturbation_unitball: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open Filter`):
--
--   ```lean
--   lemma commutator_perturbation_unitball (Y Z A : K →L[ℂ] K) {b e : ℝ}
--       (hb : ‖Z*A-A*Z‖ ≤ b) (he : ‖Y-Z‖ ≤ e) (hA : ‖A‖ ≤ 1) :
--       ‖Y*A-A*Y‖ ≤ b+2*e
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.square_symmetry_after_average` of this split imports it.
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

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma commutator_perturbation_unitball (Y Z A : K →L[ℂ] K) {b e : ℝ}
    (hb : ‖Z*A-A*Z‖ ≤ b) (he : ‖Y-Z‖ ≤ e) (hA : ‖A‖ ≤ 1) :
    ‖Y*A-A*Y‖ ≤ b+2*e := by
  sorry

end Kadison

end

end OAI
end
