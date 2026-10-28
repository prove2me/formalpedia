-- Prove2me | Theorems.Thm_OAI_Laughlin_Certificate_computeRow_14_9_13_2
-- name    : OAI.Laughlin.Certificate.computeRow_14_9_13_2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T19:34:28.236557+00:00
-- url     : https://prove2.me/theorems/249312bd-84f9-43ce-883c-94ab88ca51b4
-- title:
--   OAI.Laughlin.Certificate.computeRow_14_9_13_2: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Certificate.computeRow_14_9_13_2` of [lean/OAI/Analysis/Laughlin/FiniteFlux/ComputeRow0913Batch14.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/ComputeRow0913Batch14.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Certificate`):
--
--   ```lean
--   theorem computeRow_14_9_13_2 : RowCompute.yRowIntegralFast 14 9 13 (RowCompute.rows[2]!) =
--       (-5952936135585692111600665842806291566363019080334170914816000000 : ℤ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Certificate.RowCompute.rows` and `OAI.Laughlin.Certificate.RowCompute.yRowIntegralFast` (definitions bundle `OAIQ047L000` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Certificate.error_14` and `OAI.Laughlin.Certificate.source_error_14_13_9` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/ComputeRow0913Batch14.lean (declaration OAI.Laughlin.Certificate.computeRow_14_9_13_2)

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_14_9_13_2 : RowCompute.yRowIntegralFast 14 9 13 (RowCompute.rows[2]!) =
    (-5952936135585692111600665842806291566363019080334170914816000000 : ℤ) := by
  sorry

end Laughlin.Certificate

end OAI
end
