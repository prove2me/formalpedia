-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_14_contains_g
-- name    : OAI.SharpPlanar.IntegerGrid.row5_14_contains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T23:57:39.680874+00:00
-- url     : https://prove2.me/theorems/f9303938-dcb1-4828-96dc-8ee5a0affb0f
-- title:
--   OAI.SharpPlanar.IntegerGrid.row5_14_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerGrid.row5_14_contains` of [lean/OAI/Analysis/PlanarPacking/Grid.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerGrid`, with `open IntegerIntervals IntegerCompact`):
--
--   ```lean
--   lemma row5_14_contains_g (k : Fin 16) : (row5_14 k).Contains (quadraturePoint 5 (224+k.val))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.row5_14` (definitions bundle `OAIQ098G018` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.PointBox.Contains` (definitions bundle `OAIQ098G091` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerGrid.row5_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean (declaration OAI.SharpPlanar.IntegerGrid.row5_14_contains)

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G091

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerGrid
open IntegerIntervals IntegerCompact
lemma row5_14_contains_g (k : Fin 16) : (row5_14 k).Contains (quadraturePoint 5 (224+k.val)) := by
  sorry
end SharpPlanar.IntegerGrid

end OAI
end
