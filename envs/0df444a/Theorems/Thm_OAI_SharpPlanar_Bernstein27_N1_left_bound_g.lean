-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Bernstein27_N1_left_bound_g
-- name    : OAI.SharpPlanar.Bernstein27.N1_left.bound_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T02:28:31.249355+00:00
-- url     : https://prove2.me/theorems/64704d95-fafd-4f8a-9485-2a002296bde0
-- title:
--   OAI.SharpPlanar.Bernstein27.N1_left.bound_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Bernstein27.N1_left.bound` of [lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein27.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein27.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Bernstein27.N1_left`, with `open IntegerIntervals IntegerBasis Numerical`):
--
--   ```lean
--   lemma bound_g (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) k.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.powerToBernstein` (definitions bundle `OAIQ098G1643` of this split); `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098G1682` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Bernstein27.lean (declaration OAI.SharpPlanar.Bernstein27.N1_left.bound)

import Mathlib
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Bernstein27
open IntegerIntervals IntegerBasis Numerical
namespace N1_left
lemma bound_g (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 27 (-1/1) 2) k.val := by
  sorry
end N1_left
end SharpPlanar.Bernstein27

end OAI
end
