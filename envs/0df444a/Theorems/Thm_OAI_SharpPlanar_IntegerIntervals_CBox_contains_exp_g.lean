-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_exp_g
-- name    : OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-08T05:34:32.560046+00:00
-- url     : https://prove2.me/theorems/e13597d0-4722-4d1c-9f81-1eb08bc33a88
-- title:
--   OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma CBox.contains_exp_g {a : CBox} {z : ℂ} (hz : a.Contains z) (k : ℕ)
--       (hn : (a.scale 1 (2^k)).NormCheck 1) : (a.exp k).Contains (Complex.exp z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` and `OAI.SharpPlanar.IntegerIntervals.CBox.scale` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.exp` (definitions bundle `OAIQ098G075` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.NormCheck` (definitions bundle `OAIQ098G079` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerBasis.phaseBase_contains_g` and `OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp)

import Mathlib
import Definitions.Def_OAIQ098G075
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma CBox.contains_exp_g {a : CBox} {z : ℂ} (hz : a.Contains z) (k : ℕ)
    (hn : (a.scale 1 (2^k)).NormCheck 1) : (a.exp k).Contains (Complex.exp z) := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end
