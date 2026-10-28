-- Prove2me | Theorems.Thm_OAI_CriticalStrip_laguerre_least_inverseQuarter_lower
-- name    : OAI.CriticalStrip.laguerre_least_inverseQuarter_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T01:32:10.861844+00:00
-- url     : https://prove2.me/theorems/b3785548-187d-41bc-88a4-0d598ac0b60a
-- title:
--   OAI.CriticalStrip.laguerre_least_inverseQuarter_lower: intermediate lemma from OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalStrip.laguerre_least_inverseQuarter_lower` of [lean/OAI/Combinatorics/StripMass/StripMass/QuarterMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/QuarterMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalStrip`, with `open scoped BigOperators`, `open Set MeasureTheory`):
--
--   ```lean
--   theorem laguerre_least_inverseQuarter_lower (n : ℕ) :
--       (Real.exp (-1)/48) * ((n:ℝ)+1)^(1/2:ℝ) ≤
--         laguerreExpectation (n+1) 1 (fun r => (r 0)^(-(1/4:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalStrip.laguerreExpectation` (definitions bundle `OAIQ042S001` of this split).
--
--   **Used by.** The proof of `OAI.CriticalStrip.criticalStripMass_of_physical_identities` of this split imports it.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/QuarterMoments.lean (declaration OAI.CriticalStrip.laguerre_least_inverseQuarter_lower)

import Mathlib
import Definitions.Def_OAIQ042S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory

theorem laguerre_least_inverseQuarter_lower (n : ℕ) :
    (Real.exp (-1)/48) * ((n:ℝ)+1)^(1/2:ℝ) ≤
      laguerreExpectation (n+1) 1 (fun r => (r 0)^(-(1/4:ℝ))) := by
  sorry

end

end CriticalStrip

end OAI
end
