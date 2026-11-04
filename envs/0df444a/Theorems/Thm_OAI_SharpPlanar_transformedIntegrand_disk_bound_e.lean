-- Prove2me | Theorems.Thm_OAI_SharpPlanar_transformedIntegrand_disk_bound_e
-- name    : OAI.SharpPlanar.transformedIntegrand_disk_bound_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T05:59:13.129614+00:00
-- url     : https://prove2.me/theorems/339143a3-732d-4566-a3f6-9bfa8eee0600
-- title:
--   OAI.SharpPlanar.transformedIntegrand_disk_bound_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.transformedIntegrand_disk_bound` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open Complex`):
--
--   ```lean
--   lemma transformedIntegrand_disk_bound_e (c d : ℕ → ℝ)
--       (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
--       {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6)
--       {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
--       ‖finiteDensity c d j t * complexTransformedFactor m y ell t‖ ≤ (10:ℝ)^53
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.complexTransformedFactor`, `OAI.SharpPlanar.diskCenter` and `OAI.SharpPlanar.finiteDensity` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.transformedMoment_piece_average_error_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.transformedIntegrand_disk_bound)

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

lemma transformedIntegrand_disk_bound_e (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖finiteDensity c d j t * complexTransformedFactor m y ell t‖ ≤ (10:ℝ)^53 := by
  sorry

end SharpPlanar

end OAI
end
