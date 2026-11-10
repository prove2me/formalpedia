-- Prove2me | Theorems.Thm_OAI_SharpPlanar_mixed_40_13_g
-- name    : OAI.SharpPlanar.mixed_40_13_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T21:09:31.009886+00:00
-- url     : https://prove2.me/theorems/48c434e3-01ca-4192-a8d5-2f78d00526bd
-- title:
--   OAI.SharpPlanar.mixed_40_13_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.mixed_40_13` of [lean/OAI/Analysis/PlanarPacking/Certificate/MixedBound40.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MixedBound40.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis`):
--
--   ```lean
--   lemma mixed_40_13_g : transformTaylor 13 40/((Nat.factorial 13):ℝ)≤(1784145647367326687478989:ℝ)/1000000000000000000000000000000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.transformTaylor` (definitions bundle `OAIQ098G1697` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein40.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein40.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein40.N1_left.t11_contains_g` and `OAI.SharpPlanar.Bernstein40.N1_right.t11_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MixedBound40.lean (declaration OAI.SharpPlanar.mixed_40_13)

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
lemma mixed_40_13_g : transformTaylor 13 40/((Nat.factorial 13):ℝ)≤(1784145647367326687478989:ℝ)/1000000000000000000000000000000 := by
  sorry
end SharpPlanar

end OAI
end
