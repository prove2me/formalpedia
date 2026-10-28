-- Prove2me | Theorems.Thm_OAI_CriticalStrip_Diagram_polynomialNorthGluing_row_reflection
-- name    : OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T02:15:32.787682+00:00
-- url     : https://prove2.me/theorems/4a2b6e09-bedf-48fe-8199-655e9fb4bfac
-- title:
--   OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection: intermediate lemma from OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection` of [lean/OAI/Combinatorics/StripMass/StripMass/BottomGauge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/BottomGauge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalStrip.Diagram`, with `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem polynomialNorthGluing_row_reflection {n : ℕ} (i : Fin n) :
--       rowReflectLaurent i (polynomialNorthGluing n) = polynomialNorthGluing n
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalStrip.Diagram.Laurent` (definitions bundle `OAIQ042S000` of this split); `OAI.CriticalStrip.Diagram.rowReflectLaurent` (definitions bundle `OAIQ042S002` of this split); `OAI.CriticalStrip.Diagram.polynomialNorthGluing` (definitions bundle `OAIQ042S015` of this split).
--
--   **Used by.** The proof of `OAI.CriticalStrip.Diagram.polynomialNorthGluing_eq_archCandidate` of this split imports it.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/BottomGauge.lean (declaration OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection)

import Mathlib
import Definitions.Def_OAIQ042S015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

theorem polynomialNorthGluing_row_reflection {n : ℕ} (i : Fin n) :
    rowReflectLaurent i (polynomialNorthGluing n) = polynomialNorthGluing n := by
  sorry

end

end CriticalStrip.Diagram

end OAI
end
