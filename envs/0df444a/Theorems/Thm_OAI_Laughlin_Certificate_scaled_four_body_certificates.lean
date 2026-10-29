-- Prove2me | Theorems.Thm_OAI_Laughlin_Certificate_scaled_four_body_certificates
-- name    : OAI.Laughlin.Certificate.scaled_four_body_certificates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:50:58.836532+00:00
-- url     : https://prove2.me/theorems/a9f8fa5d-92c5-430b-8ca5-8b96af0f140f
-- title:
--   OAI.Laughlin.Certificate.scaled_four_body_certificates: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Certificate.scaled_four_body_certificates` of [lean/OAI/Analysis/Laughlin/FourBody/ScaledAll.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/ScaledAll.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Certificate`):
--
--   ```lean
--   theorem scaled_four_body_certificates (D : ℕ) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
--       (scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D).PosSemidef
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Certificate.certificateDiagonal`, `OAI.Laughlin.Certificate.scaledError` and `OAI.Laughlin.Certificate.scaledGram` (definitions bundle `OAIQ047L000` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.source_fourBody_limitpositive` of this split imports it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/ScaledAll.lean (declaration OAI.Laughlin.Certificate.scaled_four_body_certificates)

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem scaled_four_body_certificates (D : ℕ) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D).PosSemidef := by
  sorry

end Laughlin.Certificate

end OAI
end
