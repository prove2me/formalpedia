-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t12_contains_e
-- name    : OAI.SharpPlanar.Bernstein1.N1_left.t12_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T00:16:52.377196+00:00
-- url     : https://prove2.me/theorems/1ffa3f8a-1e38-4a0e-8f58-9aa361935402
-- title:
--   OAI.SharpPlanar.Bernstein1.N1_left.t12_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein1.N1_left.t12_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein1.N1_left`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma t12_contains_e : t12.Contains (sourcePower true 1 (-1/2) 2 12)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.Bernstein1.N1_left.t12` (definitions bundle `OAIQ098E129` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098E239` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Bernstein1.N1_left.bound_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein1.lean (declaration OAI.SharpPlanar.Bernstein1.N1_left.t12_contains)

import Mathlib
import Definitions.Def_OAIQ098E129
import Definitions.Def_OAIQ098E239

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Bernstein1
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_left
lemma t12_contains_e : t12.Contains (sourcePower true 1 (-1/2) 2 12) := by
  sorry
end N1_left
end SharpPlanar.Bernstein1

end OAI
end
