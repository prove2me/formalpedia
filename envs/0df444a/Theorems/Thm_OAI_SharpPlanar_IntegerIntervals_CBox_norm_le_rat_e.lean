-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_norm_le_rat_e
-- name    : OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_rat_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T23:56:58.118542+00:00
-- url     : https://prove2.me/theorems/b16ce6bd-45d8-4c88-9787-00256055ddfe
-- title:
--   OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_rat_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_rat` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`):
--
--   ```lean
--   lemma CBox.norm_le_rat_e {a : CBox} {z : ℂ} {m n : ℤ} (hz : a.Contains z)
--       (hc : a.SqNormCheck m n) : ‖z‖ ≤ (m:ℝ)/n
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.SqNormCheck` (definitions bundle `OAIQ098E092` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.IntegerIntervals.CBox.norm_le_rat)

import Mathlib
import Definitions.Def_OAIQ098E092

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerIntervals

lemma CBox.norm_le_rat_e {a : CBox} {z : ℂ} {m n : ℤ} (hz : a.Contains z)
    (hc : a.SqNormCheck m n) : ‖z‖ ≤ (m:ℝ)/n := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end
