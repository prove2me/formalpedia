-- Prove2me | Theorems.Thm_OAI_SharpPlanar_phase_exp_norm_bound_e
-- name    : OAI.SharpPlanar.phase_exp_norm_bound_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T05:43:01.325852+00:00
-- url     : https://prove2.me/theorems/3b759b67-1b9c-4afd-a95a-619811b1c8a1
-- title:
--   OAI.SharpPlanar.phase_exp_norm_bound_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.phase_exp_norm_bound` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open Complex`):
--
--   ```lean
--   lemma phase_exp_norm_bound_e {w : ℂ} {m L : ℝ} (hm : 0 ≤ m) (hw : -L ≤ w.im) :
--       ‖Complex.exp (Complex.I*Real.pi*w*m)‖ ≤ Real.exp (Real.pi*m*L)
--   ```
--
--   **Used by.** The proofs of `OAI.SharpPlanar.complexDirectFactor_disk_bound_e` and `OAI.SharpPlanar.complexTransformedFactor_disk_bound_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.phase_exp_norm_bound)

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

lemma phase_exp_norm_bound_e {w : ℂ} {m L : ℝ} (hm : 0 ≤ m) (hw : -L ≤ w.im) :
    ‖Complex.exp (Complex.I*Real.pi*w*m)‖ ≤ Real.exp (Real.pi*m*L) := by
  sorry

end SharpPlanar

end OAI
end
