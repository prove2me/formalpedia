-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein37_N0_left_bound_e
-- name    : OAI.SharpPlanar.Bernstein37.N0_left.bound_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T08:07:09.797949+00:00
-- url     : https://prove2.me/theorems/e43dea7b-0305-4eda-a135-d88eb6d2bd3d
-- title:
--   OAI.SharpPlanar.Bernstein37.N0_left.bound_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein37.N0_left.bound` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein37.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein37.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein37.N0_left`, with `open IntegerIntervals IntegerBasis Numerical CachedData`):
--
--   ```lean
--   lemma bound_e (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) k.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.powerToBernstein` (definitions bundle `OAIQ098E199` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098E239` of this split).
--
--   **Used by.** The proof of `OAI.sharp_fourier_certificate` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein37.lean (declaration OAI.SharpPlanar.Bernstein37.N0_left.bound)

import Mathlib
import Definitions.Def_OAIQ098E199
import Definitions.Def_OAIQ098E239

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Bernstein37
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_left
lemma bound_e (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 37 (-1/2) 2) k.val := by
  sorry
end N0_left
end SharpPlanar.Bernstein37

end OAI
end
