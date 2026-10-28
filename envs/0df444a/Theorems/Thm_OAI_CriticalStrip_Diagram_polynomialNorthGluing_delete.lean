-- Prove2me | Theorems.Thm_OAI_CriticalStrip_Diagram_polynomialNorthGluing_delete
-- name    : OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T02:11:39.096985+00:00
-- url     : https://prove2.me/theorems/33262f0a-5aa5-45de-adaf-5d577247443d
-- title:
--   OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete: intermediate lemma from OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete` of [lean/OAI/Combinatorics/StripMass/StripMass/SplitGluing.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/SplitGluing.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalStrip.Diagram`, with `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem polynomialNorthGluing_delete (n : ℕ) :
--       pairEvaluation n 3 (polynomialNorthGluing (n+2)) =
--         deletePairScalar n ^ 2 * deleteEvaluation n (polynomialNorthGluing n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalStrip.Diagram.Laurent`, `OAI.CriticalStrip.Diagram.SpectralField` and `OAI.CriticalStrip.Diagram.SpectralRing` (definitions bundle `OAIQ042S000` of this split); `OAI.CriticalStrip.Diagram.deleteEvaluation`, `OAI.CriticalStrip.Diagram.deletePairScalar` and `OAI.CriticalStrip.Diagram.pairEvaluation` (definitions bundle `OAIQ042S008` of this split); `OAI.CriticalStrip.Diagram.polynomialNorthGluing` (definitions bundle `OAIQ042S015` of this split).
--
--   **Used by.** The proof of `OAI.CriticalStrip.Diagram.polynomialNorthGluing_eq_archCandidate` of this split imports it.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/SplitGluing.lean (declaration OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete)

import Mathlib
import Definitions.Def_OAIQ042S015

section

attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

theorem polynomialNorthGluing_delete (n : ℕ) :
    pairEvaluation n 3 (polynomialNorthGluing (n+2)) =
      deletePairScalar n ^ 2 * deleteEvaluation n (polynomialNorthGluing n) := by
  sorry

end
end CriticalStrip.Diagram

end OAI
end
