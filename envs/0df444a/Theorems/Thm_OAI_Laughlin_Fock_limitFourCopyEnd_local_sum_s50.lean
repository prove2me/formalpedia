-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_limitFourCopyEnd_local_sum_s50
-- name    : OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:43:48.536058+00:00
-- url     : https://prove2.me/theorems/b9bdbe0f-d9d4-4e6d-aca5-d79e1fa4be41
-- title:
--   OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.limitFourCopyEnd_local_sum` of [lean/OAI/Analysis/Laughlin/Asymptotics/LimitFourLocalSum.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/LimitFourLocalSum.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`, `open Spin`):
--
--   ```lean
--   theorem limitFourCopyEnd_local_sum_s50 (Q r D : ℕ) (hDQ : D ≤ Q) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
--       limitFourCopyEnd Q r D x = ∑ b : LocalFourIndex D,
--         (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
--           limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.LocalFourIndex` and `OAI.Laughlin.Spin.fourBodyLimitCoefficient` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.limitFourEnd` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.limitFourCopyEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/LimitFourLocalSum.lean (declaration OAI.Laughlin.Fock.limitFourCopyEnd_local_sum)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourCopyEnd_local_sum_s50 (Q r D : ℕ) (hDQ : D ≤ Q) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
    limitFourCopyEnd Q r D x = ∑ b : LocalFourIndex D,
      (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
        limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x := by
  sorry

end Laughlin.Fock

end OAI
end
