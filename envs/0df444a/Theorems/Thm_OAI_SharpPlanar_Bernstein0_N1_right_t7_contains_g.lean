-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein0_N1_right_t7_contains_g
-- name    : OAI.SharpPlanar.Bernstein0.N1_right.t7_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T00:10:12.747563+00:00
-- url     : https://prove2.me/theorems/a6198a29-ec25-4b0c-b5fe-887dcee378a8
-- title:
--   OAI.SharpPlanar.Bernstein0.N1_right.t7_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein0.N1_right.t7_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein0.N1_right`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma t7_contains_g : t7.Contains (sourcePower true 0 (1/2) 0 7)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.Bernstein0.N1_right.t7` (definitions bundle `OAIQ098G382` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.halfSign_0_N1_right_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein0.lean (declaration OAI.SharpPlanar.Bernstein0.N1_right.t7_contains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Bernstein0
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
lemma t7_contains_g : t7.Contains (sourcePower true 0 (1/2) 0 7) := by
  sorry
end N1_right
end SharpPlanar.Bernstein0

end OAI
end
