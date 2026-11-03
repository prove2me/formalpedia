-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_limitSliceCoefficient_antisymmetric_s50
-- name    : OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:46:34.757757+00:00
-- url     : https://prove2.me/theorems/698e8930-30cf-4a43-9904-bc733fac3dac
-- title:
--   OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric` of [lean/OAI/Analysis/Laughlin/FourBody/SliceCoefficient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/SliceCoefficient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem limitSliceCoefficient_antisymmetric_s50 (r D p j k : ℕ) (hr : r ≤ D) (ho : Odd r) :
--       limitSliceCoefficient r D p k j = -limitSliceCoefficient r D p j k
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.limitSliceCoefficient` (definitions bundle `OAIQ050L012` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.limitFourColumn_physical_L_s50` and `OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/SliceCoefficient.lean (declaration OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric)

import Mathlib
import Definitions.Def_OAIQ050L012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem limitSliceCoefficient_antisymmetric_s50 (r D p j k : ℕ) (hr : r ≤ D) (ho : Odd r) :
    limitSliceCoefficient r D p k j = -limitSliceCoefficient r D p j k := by
  sorry

end Laughlin.Spin

end OAI
end
