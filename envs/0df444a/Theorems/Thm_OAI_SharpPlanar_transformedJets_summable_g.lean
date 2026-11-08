-- Prove2me | Theorems.Thm_OAI_SharpPlanar_transformedJets_summable_g
-- name    : OAI.SharpPlanar.transformedJets_summable_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:22:21.702177+00:00
-- url     : https://prove2.me/theorems/7d3ae36d-af46-449e-91fe-e6a339f9e818
-- title:
--   OAI.SharpPlanar.transformedJets_summable_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.transformedJets_summable` of [lean/OAI/Analysis/PlanarPacking/ContactData.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ContactData.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`):
--
--   ```lean
--   lemma transformedJets_summable_g (p : CardinalData) : Summable (fun ni => |transformedJets p ni|)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.CardinalData` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.transformedJets` (definitions bundle `OAIQ098G016` of this split).
--
--   **Used by.** The definitions bundle `OAIQ098G1648` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ContactData.lean (declaration OAI.SharpPlanar.transformedJets_summable)

import Mathlib
import Definitions.Def_OAIQ098G016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma transformedJets_summable_g (p : CardinalData) : Summable (fun ni => |transformedJets p ni|) := by
  sorry

end SharpPlanar

end OAI
end
