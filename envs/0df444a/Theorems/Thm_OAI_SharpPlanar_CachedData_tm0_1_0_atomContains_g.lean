-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_tm0_1_0_atomContains_g
-- name    : OAI.SharpPlanar.CachedData.tm0_1_0.atomContains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T04:06:03.686295+00:00
-- url     : https://prove2.me/theorems/7016bfb7-2357-4a27-babf-33c3b59b337a
-- title:
--   OAI.SharpPlanar.CachedData.tm0_1_0.atomContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.tm0_1_0.atomContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.tm0_1_0`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma atomContains_g : atomAnswer.Contains (tableMomentAtom false 1 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.tm0_1_0.atomAnswer` (definitions bundle `OAIQ098G1456` of this split); `OAI.SharpPlanar.tableMomentAtom` (definitions bundle `OAIQ098G1680` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Residual1.contains1_1_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments1.lean (declaration OAI.SharpPlanar.CachedData.tm0_1_0.atomContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1456
import Definitions.Def_OAIQ098G1680

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_1_0
lemma atomContains_g : atomAnswer.Contains (tableMomentAtom false 1 0) := by
  sorry
end tm0_1_0

end SharpPlanar.CachedData

end OAI
end
