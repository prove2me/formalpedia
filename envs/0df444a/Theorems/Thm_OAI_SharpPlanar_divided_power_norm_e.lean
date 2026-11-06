-- Prove2me | Theorems.Thm_OAI_SharpPlanar_divided_power_norm_e
-- name    : OAI.SharpPlanar.divided_power_norm_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:42:16.156041+00:00
-- url     : https://prove2.me/theorems/f9a40cb9-d3f8-458d-9977-d32635bcfa67
-- title:
--   OAI.SharpPlanar.divided_power_norm_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.divided_power_norm` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open Complex`):
--
--   ```lean
--   lemma divided_power_norm_e (w : ℂ) (ell : ℕ) :
--       ‖w^ell / (ell.factorial:ℂ)‖ ≤ Real.exp ‖w‖
--   ```
--
--   **Used by.** The proofs of `OAI.SharpPlanar.complexDirectFactor_disk_bound_e` and `OAI.SharpPlanar.complexTransformedFactor_disk_bound_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.divided_power_norm)

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

lemma divided_power_norm_e (w : ℂ) (ell : ℕ) :
    ‖w^ell / (ell.factorial:ℂ)‖ ≤ Real.exp ‖w‖ := by
  sorry

end SharpPlanar

end OAI
end
