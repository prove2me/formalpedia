-- Prove2me | Theorems.Thm_OAI_SharpPlanar_residual_finite_exterior_0_g
-- name    : OAI.SharpPlanar.residual_finite_exterior_0_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T02:31:17.101412+00:00
-- url     : https://prove2.me/theorems/c3d1ef74-843f-4a90-8244-d23515abffde
-- title:
--   OAI.SharpPlanar.residual_finite_exterior_0_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.residual_finite_exterior_0` of [lean/OAI/Analysis/PlanarPacking/ResidualFinite.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ResidualFinite.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Numerical`, `open scoped BigOperators`):
--
--   ```lean
--   lemma residual_finite_exterior_0_g (i : Fin 48 × Fin 2) : |tableResidual false (exteriorIndex i)|<(1:ℝ)/10^9
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.Numerical.exteriorIndex` (definitions bundle `OAIQ098G006` of this split); `OAI.SharpPlanar.tableResidual` (definitions bundle `OAIQ098G1696` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.residual_finite_bound_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ResidualFinite.lean (declaration OAI.SharpPlanar.residual_finite_exterior_0)

import Mathlib
import Definitions.Def_OAIQ098G006
import Definitions.Def_OAIQ098G1696

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Numerical
open scoped BigOperators
lemma residual_finite_exterior_0_g (i : Fin 48 × Fin 2) : |tableResidual false (exteriorIndex i)|<(1:ℝ)/10^9 := by
  sorry
end SharpPlanar

end OAI
end
