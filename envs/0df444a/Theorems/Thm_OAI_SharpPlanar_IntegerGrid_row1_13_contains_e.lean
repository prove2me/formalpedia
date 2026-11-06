-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_13_contains_e
-- name    : OAI.SharpPlanar.IntegerGrid.row1_13_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T23:07:31.569301+00:00
-- url     : https://prove2.me/theorems/85f28ec4-ee24-4dc7-b837-e9249b932fa4
-- title:
--   OAI.SharpPlanar.IntegerGrid.row1_13_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerGrid.row1_13_contains` of [lean/OAI/Analysis/PlanarPacking/Grid.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerGrid`, with `open IntegerIntervals IntegerCompact`):
--
--   ```lean
--   lemma row1_13_contains_e (k : Fin 16) : (row1_13 k).Contains (quadraturePoint 1 (208+k.val))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.row1_13` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.PointBox.Contains` (definitions bundle `OAIQ098E031` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerGrid.row1_contains_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean (declaration OAI.SharpPlanar.IntegerGrid.row1_13_contains)

import Mathlib
import Definitions.Def_OAIQ098E031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerGrid
open IntegerIntervals IntegerCompact
lemma row1_13_contains_e (k : Fin 16) : (row1_13 k).Contains (quadraturePoint 1 (208+k.val)) := by
  sorry
end SharpPlanar.IntegerGrid

end OAI
end
