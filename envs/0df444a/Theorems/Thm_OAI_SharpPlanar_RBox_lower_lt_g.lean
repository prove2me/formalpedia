-- Prove2me | Theorems.Thm_OAI_SharpPlanar_RBox_lower_lt_g
-- name    : OAI.SharpPlanar.RBox.lower_lt_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T19:08:16.233112+00:00
-- url     : https://prove2.me/theorems/dce0ecde-5cc1-4aa3-9075-27d670be9cee
-- title:
--   OAI.SharpPlanar.RBox.lower_lt_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.RBox.lower_lt` of [lean/OAI/Analysis/PlanarPacking/BernsteinBoxes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BernsteinBoxes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis Numerical`, `open scoped BigOperators`):
--
--   ```lean
--   lemma RBox.lower_lt_g {box : RBox} {x : ℝ} {u v : ℤ} (hh : box.Contains x)
--       (hv : 0<v) (hc : precision*u<box.lo*v) : (u:ℝ)/v<x
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox` and `OAI.SharpPlanar.IntegerIntervals.precision` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein12.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein13.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein13.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein13.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein13.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein15.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein15.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein15.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein15.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein16.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein16.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein16.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein16.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein19.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein19.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein19.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein19.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein1.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein1.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein1.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein21.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein21.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein21.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein21.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein24.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein24.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein24.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein24.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein25.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein25.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein25.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein25.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein27.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein27.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein27.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein27.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein28.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein28.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein28.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein28.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein31.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein31.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein31.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein31.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein33.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein33.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein33.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein33.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein36.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein36.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein37.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein37.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein37.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein37.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein39.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein39.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein39.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein39.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein40.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein40.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein40.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein40.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein4.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein4.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein4.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein4.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein7.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein7.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein7.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein7.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein9.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein9.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein9.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein9.N1_right.bound_g`, `OAI.SharpPlanar.exactLeft_origin_positive_g`, `OAI.SharpPlanar.halfSign_0_N1_right_g` and `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BernsteinBoxes.lean (declaration OAI.SharpPlanar.RBox.lower_lt)

import Mathlib
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
open scoped BigOperators
lemma RBox.lower_lt_g {box : RBox} {x : ℝ} {u v : ℤ} (hh : box.Contains x)
    (hv : 0<v) (hc : precision*u<box.lo*v) : (u:ℝ)/v<x := by
  sorry
end SharpPlanar

end OAI
end
