-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Residual1_contains1_1_g
-- name    : OAI.SharpPlanar.Residual1.contains1_1_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T02:20:39.444499+00:00
-- url     : https://prove2.me/theorems/300051a5-afe5-4408-bd6d-2ca58b5a7ea1
-- title:
--   OAI.SharpPlanar.Residual1.contains1_1_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Residual1.contains1_1` of [lean/OAI/Analysis/PlanarPacking/Certificate/Residual1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Residual1`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma contains1_1_g : box1_1.Contains (tableResidual true (node,true))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.Residual1.node` (definitions bundle `OAIQ098G1646` of this split); `OAI.SharpPlanar.Residual1.box1_1` (definitions bundle `OAIQ098G1657` of this split); `OAI.SharpPlanar.tableResidual` (definitions bundle `OAIQ098G1696` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.residual_finite_central_1_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual1.lean (declaration OAI.SharpPlanar.Residual1.contains1_1)

import Mathlib
import Definitions.Def_OAIQ098G1657
import Definitions.Def_OAIQ098G1696

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Residual1
open IntegerIntervals IntegerBasis Numerical CachedData
lemma contains1_1_g : box1_1.Contains (tableResidual true (node,true)) := by
  sorry
end SharpPlanar.Residual1

end OAI
end
