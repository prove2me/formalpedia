-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceFourVector_rotation_s50
-- name    : OAI.Laughlin.Fock.sourceFourVector_rotation_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T21:02:29.443939+00:00
-- url     : https://prove2.me/theorems/14042baf-141a-4129-a9d2-7bff0ebd6cd8
-- title:
--   OAI.Laughlin.Fock.sourceFourVector_rotation_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceFourVector_rotation` of [lean/OAI/Analysis/Laughlin/FourBody/FockCovariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/FockCovariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin`, `open scoped BigOperators Matrix Kronecker`):
--
--   ```lean
--   theorem sourceFourVector_rotation_s50 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) (i : FourWedgeIndex Q) :
--       exteriorRotation Q g (sourceFourVector Q i) =
--         ∑ j, fourBodySpinRepresentation Q g j i • sourceFourVector Q j
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.sourceFourVector`, `OAI.Laughlin.Spin.FourWedgeIndex` and `OAI.Laughlin.Spin.WedgePairIndex` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.exteriorRotation` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Spin.fourBodySpinRepresentation` (definitions bundle `OAIQ050L024` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceFourFamilyEnd_rotation_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/FockCovariance.lean (declaration OAI.Laughlin.Fock.sourceFourVector_rotation)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix Kronecker

theorem sourceFourVector_rotation_s50 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) (i : FourWedgeIndex Q) :
    exteriorRotation Q g (sourceFourVector Q i) =
      ∑ j, fourBodySpinRepresentation Q g j i • sourceFourVector Q j := by
  sorry

end Laughlin.Fock

end OAI
end
