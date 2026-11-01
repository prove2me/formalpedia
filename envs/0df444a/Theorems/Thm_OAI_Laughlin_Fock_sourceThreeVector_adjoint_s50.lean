-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceThreeVector_adjoint_s50
-- name    : OAI.Laughlin.Fock.sourceThreeVector_adjoint_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:54:35.119584+00:00
-- url     : https://prove2.me/theorems/9c24ce81-58b5-4ae0-8046-98368fdc0463
-- title:
--   OAI.Laughlin.Fock.sourceThreeVector_adjoint_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceThreeVector_adjoint` of [lean/OAI/Analysis/Laughlin/ThreeBody/FockHaar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/FockHaar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin MeasureTheory`, `open scoped BigOperators Matrix Kronecker`):
--
--   ```lean
--   theorem sourceThreeVector_adjoint_s50 (Q : ℕ) (i : PairOrbitalIndex Q) (x y : Space Q) :
--       occupationInner Q (sourceThreeVector Q i*x) y =
--         occupationInner Q x (sourceThreeEnd Q i y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.occupationInner` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Fock.sourceThreeEnd` and `OAI.Laughlin.Fock.sourceThreeVector` (definitions bundle `OAIQ050L017` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physical_threeBody_Fock_null_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/FockHaar.lean (declaration OAI.Laughlin.Fock.sourceThreeVector_adjoint)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix Kronecker

theorem sourceThreeVector_adjoint_s50 (Q : ℕ) (i : PairOrbitalIndex Q) (x y : Space Q) :
    occupationInner Q (sourceThreeVector Q i*x) y =
      occupationInner Q x (sourceThreeEnd Q i y) := by
  sorry

end Laughlin.Fock

end OAI
end
