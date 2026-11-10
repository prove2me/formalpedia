-- Prove2me | Theorems.Thm_OAI_SharpPlanar_sourcePower_of_cap_g
-- name    : OAI.SharpPlanar.sourcePower_of_cap_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T21:10:26.775294+00:00
-- url     : https://prove2.me/theorems/a49ec444-5a0e-4484-b99f-f5862806e554
-- title:
--   OAI.SharpPlanar.sourcePower_of_cap_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.sourcePower_of_cap` of [lean/OAI/Analysis/PlanarPacking/CoarseTaylor.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CoarseTaylor.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis`):
--
--   ```lean
--   lemma sourcePower_of_cap_g (a : Bool) (n : ℕ) (y : ℝ) (nu r : ℕ) {B : ℝ}
--       (hB : sharpTaylor (r+nu) n/((r+nu).factorial:ℝ)≤B) :
--       |sourcePower a n y nu r| ≤ |y|^r*B
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.sourcePower` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.sharpTaylor` (definitions bundle `OAIQ098G1690` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein12.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein13.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein13.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein13.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein13.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein15.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein15.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein15.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein15.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein16.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein16.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein16.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein16.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein19.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein19.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein19.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein19.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein21.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein21.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein21.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein21.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein24.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein24.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein24.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein24.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein25.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein25.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein25.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein25.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein27.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein27.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein27.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein27.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein28.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein28.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein28.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein28.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein31.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein31.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein31.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein31.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein33.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein33.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein33.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein33.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein36.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein36.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein36.N1_left.ts_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_right.ts_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein37.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein37.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein37.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein39.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein39.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein39.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein39.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein40.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein40.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein40.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein40.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein4.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein4.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein4.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein4.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein7.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein7.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein7.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein7.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein9.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein9.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein9.N1_left.bound_g` and `OAI.SharpPlanar.Bernstein9.N1_right.bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CoarseTaylor.lean (declaration OAI.SharpPlanar.sourcePower_of_cap)

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
lemma sourcePower_of_cap_g (a : Bool) (n : ℕ) (y : ℝ) (nu r : ℕ) {B : ℝ}
    (hB : sharpTaylor (r+nu) n/((r+nu).factorial:ℝ)≤B) :
    |sourcePower a n y nu r| ≤ |y|^r*B := by
  sorry
end SharpPlanar

end OAI
end
