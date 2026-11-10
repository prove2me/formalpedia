-- Prove2me | Theorems.Thm_OAI_SharpPlanar_coarse_3_29_g
-- name    : OAI.SharpPlanar.coarse_3_29_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T21:06:50.672701+00:00
-- url     : https://prove2.me/theorems/b1059e28-26ad-41c7-a0a6-1f180cdd29fd
-- title:
--   OAI.SharpPlanar.coarse_3_29_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.coarse_3_29` of [lean/OAI/Analysis/PlanarPacking/Certificate/CoarseBound3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/CoarseBound3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis`):
--
--   ```lean
--   lemma coarse_3_29_g : sharpTaylor 29 3/((Nat.factorial 29):ℝ)≤(1167001043399812052418:ℝ)/1000000000000000000000000000000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.sharpTaylor` (definitions bundle `OAIQ098G1690` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein3.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_left.bound_g` and `OAI.SharpPlanar.Bernstein3.N1_right.bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/CoarseBound3.lean (declaration OAI.SharpPlanar.coarse_3_29)

import Mathlib
import Definitions.Def_OAIQ098G1690

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma coarse_3_29_g : sharpTaylor 29 3/((Nat.factorial 29):ℝ)≤(1167001043399812052418:ℝ)/1000000000000000000000000000000 := by
  sorry
end SharpPlanar

end OAI
end
