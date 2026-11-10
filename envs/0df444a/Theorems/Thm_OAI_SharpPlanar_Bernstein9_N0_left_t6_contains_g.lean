-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein9_N0_left_t6_contains_g
-- name    : OAI.SharpPlanar.Bernstein9.N0_left.t6_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T03:42:30.506299+00:00
-- url     : https://prove2.me/theorems/96028441-37f8-4d0b-a8ca-da0fb9588d28
-- title:
--   OAI.SharpPlanar.Bernstein9.N0_left.t6_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein9.N0_left.t6_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein9.N0_left`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma t6_contains_g : t6.Contains (sourcePower false 9 (-1/1) 2 6)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.Bernstein9.N0_left.t6` (definitions bundle `OAIQ098G382` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Bernstein9.N0_left.bound_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein9.lean (declaration OAI.SharpPlanar.Bernstein9.N0_left.t6_contains)

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

namespace SharpPlanar.Bernstein9
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_left
lemma t6_contains_g : t6.Contains (sourcePower false 9 (-1/1) 2 6) := by
  sorry
end N0_left
end SharpPlanar.Bernstein9

end OAI
end
