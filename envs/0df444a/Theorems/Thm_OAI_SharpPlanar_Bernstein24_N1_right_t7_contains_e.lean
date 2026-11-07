-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein24_N1_right_t7_contains_e
-- name    : OAI.SharpPlanar.Bernstein24.N1_right.t7_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T05:22:44.0442+00:00
-- url     : https://prove2.me/theorems/f3d10a08-bd34-438f-8526-07c030b5f165
-- title:
--   OAI.SharpPlanar.Bernstein24.N1_right.t7_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein24.N1_right.t7_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein24.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein24.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein24.N1_right`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma t7_contains_e : t7.Contains (sourcePower true 24 (1/2) 2 7)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.Bernstein24.N1_right.t7` (definitions bundle `OAIQ098E129` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098E239` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Bernstein24.N1_right.bound_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein24.lean (declaration OAI.SharpPlanar.Bernstein24.N1_right.t7_contains)

import Mathlib
import Definitions.Def_OAIQ098E129
import Definitions.Def_OAIQ098E239

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Bernstein24
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
lemma t7_contains_e : t7.Contains (sourcePower true 24 (1/2) 2 7) := by
  sorry
end N1_right
end SharpPlanar.Bernstein24

end OAI
end
