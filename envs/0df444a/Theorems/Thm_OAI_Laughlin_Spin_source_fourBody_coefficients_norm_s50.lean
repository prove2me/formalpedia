-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_coefficients_norm_s50
-- name    : OAI.Laughlin.Spin.source_fourBody_coefficients_norm_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:48:26.884324+00:00
-- url     : https://prove2.me/theorems/33b6aa35-1429-4f6b-b2b7-724d8f73547b
-- title:
--   OAI.Laughlin.Spin.source_fourBody_coefficients_norm_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.source_fourBody_coefficients_norm` of [lean/OAI/Analysis/Laughlin/FourBody/CoefficientNorm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/CoefficientNorm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem source_fourBody_coefficients_norm_s50 (Q r D T : ℕ) (ho : Odd r)
--       (hrD : r ≤ D) (hDT : D ≤ T) (hQT : T+2 ≤ Q) :
--       (∑ p : Fin ((2*Q-2)+1), ∑ i : WedgePairIndex Q,
--         if p.val+i.val.1.val+i.val.2.val=T then
--           (fourBodyCoefficient Q r D T p.val i.val.1.val i.val.2.val)^2 else 0) = 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Spin.fourBodyCoefficient` (definitions bundle `OAIQ050L010` of this split); `OAI.Laughlin.Spin.WedgePairIndex` (definitions bundle `OAIQ050L012` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Spin.source_fourBody_local_normalization_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/CoefficientNorm.lean (declaration OAI.Laughlin.Spin.source_fourBody_coefficients_norm)

import Mathlib
import Definitions.Def_OAIQ050L010
import Definitions.Def_OAIQ050L012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_coefficients_norm_s50 (Q r D T : ℕ) (ho : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hQT : T+2 ≤ Q) :
    (∑ p : Fin ((2*Q-2)+1), ∑ i : WedgePairIndex Q,
      if p.val+i.val.1.val+i.val.2.val=T then
        (fourBodyCoefficient Q r D T p.val i.val.1.val i.val.2.val)^2 else 0) = 1 := by
  sorry

end Laughlin.Spin

end OAI
end
