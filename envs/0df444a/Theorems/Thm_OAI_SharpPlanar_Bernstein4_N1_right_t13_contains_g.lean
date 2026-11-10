-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t13_contains_g
-- name    : OAI.SharpPlanar.Bernstein4.N1_right.t13_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T03:23:40.250229+00:00
-- url     : https://prove2.me/theorems/50842c2e-a284-495a-88c8-9f9f2524e36a
-- title:
--   OAI.SharpPlanar.Bernstein4.N1_right.t13_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein4.N1_right.t13_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein4.N1_right`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma t13_contains_g : t13.Contains (sourcePower true 4 (3/2) 2 13)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.Bernstein4.N1_right.t13` (definitions bundle `OAIQ098G382` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Bernstein4.N1_right.bound_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein4.lean (declaration OAI.SharpPlanar.Bernstein4.N1_right.t13_contains)

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

namespace SharpPlanar.Bernstein4
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
lemma t13_contains_g : t13.Contains (sourcePower true 4 (3/2) 2 13) := by
  sorry
end N1_right
end SharpPlanar.Bernstein4

end OAI
end
