-- Prove2me | Theorems.Thm_OAI_SharpPlanar_exp_segment_bound_e
-- name    : OAI.SharpPlanar.exp_segment_bound_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T05:42:17.999367+00:00
-- url     : https://prove2.me/theorems/f417ea48-af89-4e14-a899-477c4c8d8c7d
-- title:
--   OAI.SharpPlanar.exp_segment_bound_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.exp_segment_bound` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`):
--
--   ```lean
--   lemma exp_segment_bound_e {a l u : ℝ} (ha : 0 ≤ a) (hlu : l ≤ u) :
--       (∫ t in l..u, Real.exp (-a*(u-t))) ≤ if a=0 then u-l else min (u-l) (1/a)
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.segment_exp_integral_bound_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.exp_segment_bound)

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

lemma exp_segment_bound_e {a l u : ℝ} (ha : 0 ≤ a) (hlu : l ≤ u) :
    (∫ t in l..u, Real.exp (-a*(u-t))) ≤ if a=0 then u-l else min (u-l) (1/a) := by
  sorry

end SharpPlanar

end OAI
end
