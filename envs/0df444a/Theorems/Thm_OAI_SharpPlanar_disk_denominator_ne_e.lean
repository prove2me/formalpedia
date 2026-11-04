-- Prove2me | Theorems.Thm_OAI_SharpPlanar_disk_denominator_ne_e
-- name    : OAI.SharpPlanar.disk_denominator_ne_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T05:55:31.926622+00:00
-- url     : https://prove2.me/theorems/b0e89d8a-f656-47ca-9bb5-1f6ea42f68b7
-- title:
--   OAI.SharpPlanar.disk_denominator_ne_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.disk_denominator_ne` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open Complex`):
--
--   ```lean
--   lemma disk_denominator_ne_e {j : ℕ} (hj : j < 6) {t : ℂ}
--       (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : t+Complex.I*(h:ℂ) ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.h` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.diskCenter` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.disk_z_imaginary_e` and `OAI.SharpPlanar.transformedIntegrand_analytic_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.disk_denominator_ne)

import Mathlib
import Definitions.Def_OAIQ098E018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open Complex

lemma disk_denominator_ne_e {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : t+Complex.I*(h:ℂ) ≠ 0 := by
  sorry

end SharpPlanar

end OAI
end
