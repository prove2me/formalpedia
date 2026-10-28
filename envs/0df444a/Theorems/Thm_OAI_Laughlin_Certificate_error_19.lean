-- Prove2me | Theorems.Thm_OAI_Laughlin_Certificate_error_19
-- name    : OAI.Laughlin.Certificate.error_19
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:56.99235+00:00
-- url     : https://prove2.me/theorems/adad4feb-2de5-40d6-acfc-17003185fb10
-- title:
--   OAI.Laughlin.Certificate.error_19: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Certificate.error_19` of [lean/OAI/Analysis/Laughlin/FiniteFlux/GramData19.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/GramData19.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Certificate`):
--
--   ```lean
--   theorem error_19 : errorRational 19 = candidateY_19
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Certificate.candidateY_19` and `OAI.Laughlin.Certificate.errorRational` (definitions bundle `OAIQ047L000` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Certificate.four_body_19_positive` of this split imports it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/GramData19.lean (declaration OAI.Laughlin.Certificate.error_19)

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem error_19 : errorRational 19 = candidateY_19 := by
  sorry

end Laughlin.Certificate

end OAI
end
