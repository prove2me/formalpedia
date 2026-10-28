-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_limitFourCopyEnd_local_sum
-- name    : OAI.Laughlin.Fock.limitFourCopyEnd_local_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:30:41.802283+00:00
-- url     : https://prove2.me/theorems/c3832222-8bf4-491a-9455-b211c809320e
-- title:
--   OAI.Laughlin.Fock.limitFourCopyEnd_local_sum: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.limitFourCopyEnd_local_sum` of [lean/OAI/Analysis/Laughlin/Asymptotics/LimitFourLocalSum.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/LimitFourLocalSum.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`, `open Spin`):
--
--   ```lean
--   theorem limitFourCopyEnd_local_sum (Q r D : ℕ) (hDQ : D ≤ Q) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
--       limitFourCopyEnd Q r D x = ∑ b : LocalFourIndex D,
--         (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
--           limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space`, `OAI.Laughlin.Spin.LocalFourIndex` and `OAI.Laughlin.Spin.fourBodyLimitCoefficient` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Fock.limitFourCopyEnd` and `OAI.Laughlin.Fock.limitFourEnd` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physical_fourBody_total_haar_transfer` and `OAI_Laughlin_Fock_source_fourBody_uniform_transfer` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/LimitFourLocalSum.lean (declaration OAI.Laughlin.Fock.limitFourCopyEnd_local_sum)

import Mathlib
import Definitions.Def_OAIQ047L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourCopyEnd_local_sum (Q r D : ℕ) (hDQ : D ≤ Q) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
    limitFourCopyEnd Q r D x = ∑ b : LocalFourIndex D,
      (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
        limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x := by
  sorry

end Laughlin.Fock

end OAI
end
