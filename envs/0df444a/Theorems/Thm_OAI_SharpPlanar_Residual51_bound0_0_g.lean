-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Residual51_bound0_0_g
-- name    : OAI.SharpPlanar.Residual51.bound0_0_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T10:01:36.634861+00:00
-- url     : https://prove2.me/theorems/5009465d-29ec-4379-a423-486716d6fc5e
-- title:
--   OAI.SharpPlanar.Residual51.bound0_0_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Residual51.bound0_0` of [lean/OAI/Analysis/PlanarPacking/Certificate/Residual51.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual51.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Residual51`, with `open Numerical`):
--
--   ```lean
--   lemma bound0_0_g : |tableResidual false (node,false)| < (1:ℝ)/10^9
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.Residual51.node` (definitions bundle `OAIQ098G1646` of this split); `OAI.SharpPlanar.tableResidual` (definitions bundle `OAIQ098G1696` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.residual_finite_exterior_0_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual51.lean (declaration OAI.SharpPlanar.Residual51.bound0_0)

import Mathlib
import Definitions.Def_OAIQ098G1696

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Residual51
open Numerical
lemma bound0_0_g : |tableResidual false (node,false)| < (1:ℝ)/10^9 := by
  sorry
end SharpPlanar.Residual51

end OAI
end
