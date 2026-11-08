-- Prove2me | Theorems.Thm_OAI_SharpPlanar_disk_delta_bounds_g
-- name    : OAI.SharpPlanar.disk_delta_bounds_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:14:44.404222+00:00
-- url     : https://prove2.me/theorems/03f1ac5b-c1b1-4b8a-951e-a9ef7ee498fb
-- title:
--   OAI.SharpPlanar.disk_delta_bounds_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.disk_delta_bounds` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open Complex`):
--
--   ```lean
--   lemma disk_delta_bounds_g {j : ℕ} (hj : j < 6) :
--       167/1200 ≤ Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ∧
--       Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ≤ 389/400
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.h` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.diskCenter` (definitions bundle `OAIQ098G072` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.disk_z_imaginary_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.disk_delta_bounds)

import Mathlib
import Definitions.Def_OAIQ098G072

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

lemma disk_delta_bounds_g {j : ℕ} (hj : j < 6) :
    167/1200 ≤ Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ∧
    Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ≤ 389/400 := by
  sorry

end SharpPlanar

end OAI
end
