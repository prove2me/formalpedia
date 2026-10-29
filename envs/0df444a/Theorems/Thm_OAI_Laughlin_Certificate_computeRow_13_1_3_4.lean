-- Prove2me | Theorems.Thm_OAI_Laughlin_Certificate_computeRow_13_1_3_4
-- name    : OAI.Laughlin.Certificate.computeRow_13_1_3_4
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T19:13:34.425962+00:00
-- url     : https://prove2.me/theorems/e2f96560-befe-42d8-869f-e29e5404a611
-- title:
--   OAI.Laughlin.Certificate.computeRow_13_1_3_4: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Certificate.computeRow_13_1_3_4` of [lean/OAI/Analysis/Laughlin/FiniteFlux/ComputeRow0103Batch13.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/ComputeRow0103Batch13.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Certificate`):
--
--   ```lean
--   theorem computeRow_13_1_3_4 : RowCompute.yRowIntegralFast 13 1 3 (RowCompute.rows[4]!) =
--       (175166574423452065720552273661311293783748709399295688704000000 : ℤ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Certificate.RowCompute.rows` and `OAI.Laughlin.Certificate.RowCompute.yRowIntegralFast` (definitions bundle `OAIQ047L000` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Certificate.error_13` and `OAI.Laughlin.Certificate.source_error_13_3_1` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/ComputeRow0103Batch13.lean (declaration OAI.Laughlin.Certificate.computeRow_13_1_3_4)

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_13_1_3_4 : RowCompute.yRowIntegralFast 13 1 3 (RowCompute.rows[4]!) =
    (175166574423452065720552273661311293783748709399295688704000000 : ℤ) := by
  sorry

end Laughlin.Certificate

end OAI
end
