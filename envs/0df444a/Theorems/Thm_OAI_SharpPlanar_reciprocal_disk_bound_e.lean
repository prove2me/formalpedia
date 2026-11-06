-- Prove2me | Theorems.Thm_OAI_SharpPlanar_reciprocal_disk_bound_e
-- name    : OAI.SharpPlanar.reciprocal_disk_bound_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:43:24.577492+00:00
-- url     : https://prove2.me/theorems/355a379e-a35c-44ff-9eed-f97e0a6451b1
-- title:
--   OAI.SharpPlanar.reciprocal_disk_bound_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.reciprocal_disk_bound` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open Complex`):
--
--   ```lean
--   lemma reciprocal_disk_bound_e {a u : ℂ} {r : ℝ} (hr : 0 ≤ r)
--       (hΔ : 0 < Complex.normSq a-r^2) (hu : ‖u-a‖ ≤ r) (hu0 : u ≠ 0) :
--       ‖u⁻¹-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a‖ ≤ r/(Complex.normSq a-r^2)
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.disk_z_imaginary_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.reciprocal_disk_bound)

import Mathlib

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

lemma reciprocal_disk_bound_e {a u : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hΔ : 0 < Complex.normSq a-r^2) (hu : ‖u-a‖ ≤ r) (hu0 : u ≠ 0) :
    ‖u⁻¹-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a‖ ≤ r/(Complex.normSq a-r^2) := by
  sorry

end SharpPlanar

end OAI
end
