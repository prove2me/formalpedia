-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_annihilate_coordinate_s50
-- name    : OAI.Laughlin.Fock.annihilate_coordinate_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:42:20.217271+00:00
-- url     : https://prove2.me/theorems/adb973e0-2ebb-431a-acd0-cdb8d275c3fb
-- title:
--   OAI.Laughlin.Fock.annihilate_coordinate_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.annihilate_coordinate` of [lean/OAI/Analysis/Laughlin/Fock/Coordinates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/Coordinates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem annihilate_coordinate_s50 (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
--       (A : Finset (Fin (Q+1))) :
--       (occupationBasis Q).repr (annihilate i x) A =
--         if i ∈ A then 0 else insertionSign Q i A * (occupationBasis Q).repr x (insert i A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.insertionSign` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space`, `OAI.Laughlin.Fock.annihilate` and `OAI.Laughlin.Fock.occupationBasis` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.annihilate_create_inner_s50`, `OAI.Laughlin.Fock.create_create_inner_s50`, `OAI.Laughlin.Fock.fourOccupation_adjoint_s50`, `OAI.Laughlin.Fock.limitFourColumn_adjoint_s50`, `OAI.Laughlin.Fock.limitFourColumn_mul_adjoint_s50`, `OAI.Laughlin.Fock.localFourOperators_bound_s50`, `OAI.Laughlin.Fock.pairCreate_pair_adjoint_s50`, `OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50`, `OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50`, `OAI.Laughlin.Fock.row_normal_square_s50`, `OAI.Laughlin.Fock.sourceFourVector_adjoint_s50`, `OAI.Laughlin.Fock.sourceThreeVector_adjoint_s50` and `OAI.Laughlin.Fock.vectorCreate_adjoint_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/Coordinates.lean (declaration OAI.Laughlin.Fock.annihilate_coordinate)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_coordinate_s50 (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (annihilate i x) A =
      if i ∈ A then 0 else insertionSign Q i A * (occupationBasis Q).repr x (insert i A) := by
  sorry

end Laughlin.Fock

end OAI
end
