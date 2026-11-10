-- Prove2me | Theorems.Thm_OAI_SharpPlanar_mixed_37_10_g
-- name    : OAI.SharpPlanar.mixed_37_10_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T21:09:00.372899+00:00
-- url     : https://prove2.me/theorems/2d4b924b-26de-4ae7-a96c-e49482c9c934
-- title:
--   OAI.SharpPlanar.mixed_37_10_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.mixed_37_10` of [lean/OAI/Analysis/PlanarPacking/Certificate/MixedBound37.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MixedBound37.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis`):
--
--   ```lean
--   lemma mixed_37_10_g : transformTaylor 10 37/((Nat.factorial 10):ℝ)≤(82522924134594386764164681:ℝ)/1000000000000000000000000000000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.transformTaylor` (definitions bundle `OAIQ098G1697` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein37.N0_left.tr8_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_left.t8_contains_g` and `OAI.SharpPlanar.Bernstein37.N1_right.t8_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MixedBound37.lean (declaration OAI.SharpPlanar.mixed_37_10)

import Mathlib
import Definitions.Def_OAIQ098G1697

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma mixed_37_10_g : transformTaylor 10 37/((Nat.factorial 10):ℝ)≤(82522924134594386764164681:ℝ)/1000000000000000000000000000000 := by
  sorry
end SharpPlanar

end OAI
end
