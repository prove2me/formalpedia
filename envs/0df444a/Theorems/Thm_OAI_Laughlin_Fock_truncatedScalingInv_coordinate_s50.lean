-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_truncatedScalingInv_coordinate_s50
-- name    : OAI.Laughlin.Fock.truncatedScalingInv_coordinate_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:55:40.299818+00:00
-- url     : https://prove2.me/theorems/66158815-52f3-4ab6-8f52-80ec897d095f
-- title:
--   OAI.Laughlin.Fock.truncatedScalingInv_coordinate_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.truncatedScalingInv_coordinate` of [lean/OAI/Analysis/Laughlin/Asymptotics/TruncatedScaling.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/TruncatedScaling.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem truncatedScalingInv_coordinate_s50 (L Q : ℕ) (x : Space Q) (A : Finset (Fin (Q+1))) :
--       (occupationBasis Q).repr (truncatedScalingInv L Q x) A =
--         ((truncatedDiagonals L Q A)⁻¹ : ℝ) * (occupationBasis Q).repr x A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.truncatedDiagonals` and `OAI.Laughlin.Fock.truncatedScalingInv` (definitions bundle `OAIQ050L017` of this split); `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space` and `OAI.Laughlin.Fock.occupationBasis` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.truncatedQuadratic_error_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/TruncatedScaling.lean (declaration OAI.Laughlin.Fock.truncatedScalingInv_coordinate)

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
open scoped BigOperators

theorem truncatedScalingInv_coordinate_s50 (L Q : ℕ) (x : Space Q) (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (truncatedScalingInv L Q x) A =
      ((truncatedDiagonals L Q A)⁻¹ : ℝ) * (occupationBasis Q).repr x A := by
  sorry

end Laughlin.Fock

end OAI
end
