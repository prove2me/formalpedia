-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_exteriorRotation_unitary_s50
-- name    : OAI.Laughlin.Fock.exteriorRotation_unitary_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:50:49.030934+00:00
-- url     : https://prove2.me/theorems/b98a2b56-e178-438f-84ed-e21904451224
-- title:
--   OAI.Laughlin.Fock.exteriorRotation_unitary_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.exteriorRotation_unitary` of [lean/OAI/Analysis/Laughlin/Exterior/SpinUnitary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Exterior/SpinUnitary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation`, `open scoped BigOperators`):
--
--   ```lean
--   theorem exteriorRotation_unitary_s50 (Q : ℕ) (g : SourceSU2) (x y : Space Q) :
--       occupationInner Q (exteriorRotation Q g x) (exteriorRotation Q g y) = occupationInner Q x y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.occupationInner` and `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.exteriorRotation` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.contractionForm_haar_s50` and `OAI.Laughlin.Fock.exteriorFamily_contraction_rotation_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Exterior/SpinUnitary.lean (declaration OAI.Laughlin.Fock.exteriorRotation_unitary)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem exteriorRotation_unitary_s50 (Q : ℕ) (g : SourceSU2) (x y : Space Q) :
    occupationInner Q (exteriorRotation Q g x) (exteriorRotation Q g y) = occupationInner Q x y := by
  sorry

end Laughlin.Fock

end OAI
end
