-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_admissible_parameters_q68
-- name    : OAI.PiExponent.exists_admissible_parameters_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:19:28.832838+00:00
-- url     : https://prove2.me/theorems/687b93c9-d32c-4b42-84a9-65a0b03587bb
-- title:
--   OAI.PiExponent.exists_admissible_parameters_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.exists_admissible_parameters` of [lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent`):
--
--   ```lean
--   theorem exists_admissible_parameters_q68
--       (nu Lambda c : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
--       (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
--         Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
--       Nonempty (AdmissibleParameters nu Lambda c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.AdmissibleParameters` (definitions bundle `OAIQ068A000` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.piEventualLowerBound_of_globalInterpolation_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean (declaration OAI.PiExponent.exists_admissible_parameters)

import Mathlib
import Definitions.Def_OAIQ068A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

theorem exists_admissible_parameters_q68
    (nu Lambda c : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (AdmissibleParameters nu Lambda c) := by
  sorry

end PiExponent

end OAI
end
