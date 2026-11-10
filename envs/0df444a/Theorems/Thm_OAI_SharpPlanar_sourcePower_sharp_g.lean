-- Prove2me | Theorems.Thm_OAI_SharpPlanar_sourcePower_sharp_g
-- name    : OAI.SharpPlanar.sourcePower_sharp_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T21:10:23.044234+00:00
-- url     : https://prove2.me/theorems/d397da3e-fed1-4cf8-a389-52a9523debd0
-- title:
--   OAI.SharpPlanar.sourcePower_sharp_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.sourcePower_sharp` of [lean/OAI/Analysis/PlanarPacking/CoarseTaylor.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CoarseTaylor.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis`):
--
--   ```lean
--   lemma sourcePower_sharp_g (a : Bool) (n : ℕ) (y : ℝ) (nu r : ℕ) :
--       |sourcePower a n y nu r| ≤ |y|^r*sharpTaylor (r+nu) n/((r+nu).factorial:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.sharpTaylor` (definitions bundle `OAIQ098G1690` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.sourcePower_of_cap_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CoarseTaylor.lean (declaration OAI.SharpPlanar.sourcePower_sharp)

import Mathlib
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1690

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma sourcePower_sharp_g (a : Bool) (n : ℕ) (y : ℝ) (nu r : ℕ) :
    |sourcePower a n y nu r| ≤ |y|^r*sharpTaylor (r+nu) n/((r+nu).factorial:ℝ) := by
  sorry
end SharpPlanar

end OAI
end
