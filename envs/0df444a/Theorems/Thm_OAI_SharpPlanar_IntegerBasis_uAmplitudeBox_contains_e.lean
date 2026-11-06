-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerBasis_uAmplitudeBox_contains_e
-- name    : OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T04:50:29.53084+00:00
-- url     : https://prove2.me/theorems/2052f2f8-20f0-4d98-a4b1-f27f58425765
-- title:
--   OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerBasis`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerIntervals IntegerAlpha`):
--
--   ```lean
--   lemma uAmplitudeBox_contains_e {t : RBox} {a b : CBox} {s : ℝ} {n j : ℕ}
--       (ht : t.Contains s) (ha : a.Contains (basisAlpha n j)) (hb : b.Contains (basisBeta n j)) :
--       (uAmplitudeBox t a b).Contains (uAmplitude n j s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` and `OAI.SharpPlanar.IntegerIntervals.RBox` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerBasis.basisAlpha` and `OAI.SharpPlanar.IntegerBasis.basisBeta` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.IntegerBasis.uAmplitudeBox` (definitions bundle `OAIQ098E087` of this split); `OAI.SharpPlanar.IntegerBasis.uAmplitude` (definitions bundle `OAIQ098E111` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.IntegerBasis.uAmplitudeBox_contains)

import Mathlib
import Definitions.Def_OAIQ098E087
import Definitions.Def_OAIQ098E111

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma uAmplitudeBox_contains_e {t : RBox} {a b : CBox} {s : ℝ} {n j : ℕ}
    (ht : t.Contains s) (ha : a.Contains (basisAlpha n j)) (hb : b.Contains (basisBeta n j)) :
    (uAmplitudeBox t a b).Contains (uAmplitude n j s) := by
  sorry

end SharpPlanar.IntegerBasis

end OAI
end
