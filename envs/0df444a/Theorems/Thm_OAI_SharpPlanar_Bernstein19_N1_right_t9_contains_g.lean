-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein19_N1_right_t9_contains_g
-- name    : OAI.SharpPlanar.Bernstein19.N1_right.t9_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T02:05:59.237799+00:00
-- url     : https://prove2.me/theorems/c699e396-d1c0-4e6a-bf44-ece589de3bff
-- title:
--   OAI.SharpPlanar.Bernstein19.N1_right.t9_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein19.N1_right.t9_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein19.N1_right`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma t9_contains_g : t9.Contains (sourcePower true 19 (1/1) 2 9)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.Bernstein19.N1_right.t9` (definitions bundle `OAIQ098G382` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Bernstein19.N1_right.bound_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein19.lean (declaration OAI.SharpPlanar.Bernstein19.N1_right.t9_contains)

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

namespace SharpPlanar.Bernstein19
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
lemma t9_contains_g : t9.Contains (sourcePower true 19 (1/1) 2 9) := by
  sorry
end N1_right
end SharpPlanar.Bernstein19

end OAI
end
