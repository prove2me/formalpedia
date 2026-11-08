-- Prove2me | Theorems.Thm_OAI_SharpPlanar_frequency_distance_le_g
-- name    : OAI.SharpPlanar.frequency_distance_le_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T16:25:12.56191+00:00
-- url     : https://prove2.me/theorems/ed5049fe-9473-4a94-80de-d3bd1d740936
-- title:
--   OAI.SharpPlanar.frequency_distance_le_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.frequency_distance_le` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`):
--
--   ```lean
--   lemma frequency_distance_le_g {l : ℕ} (hl : l ≤ 6) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
--       ‖(l : ℂ)/6 - (t : ℂ)‖ ≤ 1
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.u_bound_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.frequency_distance_le)

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

lemma frequency_distance_le_g {l : ℕ} (hl : l ≤ 6) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(l : ℂ)/6 - (t : ℂ)‖ ≤ 1 := by
  sorry

end SharpPlanar

end OAI
end
