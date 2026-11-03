-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_pairCreate_pair_adjoint_s50
-- name    : OAI.Laughlin.Fock.pairCreate_pair_adjoint_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:44:15.7562+00:00
-- url     : https://prove2.me/theorems/06c3e1a1-e707-49e6-90c9-68ccd2da04cc
-- title:
--   OAI.Laughlin.Fock.pairCreate_pair_adjoint_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.pairCreate_pair_adjoint` of [lean/OAI/Analysis/Laughlin/Fock/Hamiltonian.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/Hamiltonian.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem pairCreate_pair_adjoint_s50 (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
--       (x y : Space Q) :
--       occupationInner Q (pairCreateEnd Q c x) y = occupationInner Q x (pairEnd Q c y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.occupationInner` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.pairEnd` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.pairCreateEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.sourceFourVector_adjoint_s50`, `OAI.Laughlin.Fock.sourcePairCreate_inner_s50`, `OAI.Laughlin.Fock.sourcePairEnd_rotation_s50`, `OAI.Laughlin.Fock.sourceThreeVector_adjoint_s50`, `OAI.Laughlin.Fock.threeBodyColumn_gram_s50` and `OAI.Laughlin.Planar.finite_degree_endpoint_of_fock_square_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/Hamiltonian.lean (declaration OAI.Laughlin.Fock.pairCreate_pair_adjoint)

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

theorem pairCreate_pair_adjoint_s50 (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (x y : Space Q) :
    occupationInner Q (pairCreateEnd Q c x) y = occupationInner Q x (pairEnd Q c y) := by
  sorry

end Laughlin.Fock

end OAI
end
