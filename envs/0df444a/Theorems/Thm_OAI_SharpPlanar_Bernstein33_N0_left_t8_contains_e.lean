-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein33_N0_left_t8_contains_e
-- name    : OAI.SharpPlanar.Bernstein33.N0_left.t8_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T07:24:30.312899+00:00
-- url     : https://prove2.me/theorems/3b680dd9-bfd5-44b6-9807-e20eeb781d6c
-- title:
--   OAI.SharpPlanar.Bernstein33.N0_left.t8_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein33.N0_left.t8_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein33.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein33.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein33.N0_left`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma t8_contains_e : t8.Contains (sourcePower false 33 (-1/1) 2 8)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.Bernstein33.N0_left.t8` (definitions bundle `OAIQ098E129` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098E239` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein33.N0_left.bound27_e`, `OAI.SharpPlanar.Bernstein33.N0_left.bound28_e` and `OAI.SharpPlanar.Bernstein33.N0_left.bound_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein33.lean (declaration OAI.SharpPlanar.Bernstein33.N0_left.t8_contains)

import Mathlib
import Definitions.Def_OAIQ098E129
import Definitions.Def_OAIQ098E239

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Bernstein33
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_left
lemma t8_contains_e : t8.Contains (sourcePower false 33 (-1/1) 2 8) := by
  sorry
end N0_left
end SharpPlanar.Bernstein33

end OAI
end
