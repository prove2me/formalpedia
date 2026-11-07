-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein13_N0_right_t4_contains_e
-- name    : OAI.SharpPlanar.Bernstein13.N0_right.t4_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T01:57:44.018916+00:00
-- url     : https://prove2.me/theorems/fa7e06f3-fede-40ff-ab8d-adf6713c8c38
-- title:
--   OAI.SharpPlanar.Bernstein13.N0_right.t4_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein13.N0_right.t4_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein13.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein13.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein13.N0_right`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma t4_contains_e : t4.Contains (sourcePower false 13 (1/1) 2 4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.Bernstein13.N0_right.t4` (definitions bundle `OAIQ098E129` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098E239` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Bernstein13.N0_right.bound_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein13.lean (declaration OAI.SharpPlanar.Bernstein13.N0_right.t4_contains)

import Mathlib
import Definitions.Def_OAIQ098E129
import Definitions.Def_OAIQ098E239

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Bernstein13
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
lemma t4_contains_e : t4.Contains (sourcePower false 13 (1/1) 2 4) := by
  sorry
end N0_right
end SharpPlanar.Bernstein13

end OAI
end
