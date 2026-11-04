-- Prove2me | Theorems.Thm_OAI_SharpPlanar_diskAffine_mem_e
-- name    : OAI.SharpPlanar.diskAffine_mem_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T05:54:42.732753+00:00
-- url     : https://prove2.me/theorems/59abf8dc-4237-4559-ac74-644fc59a049b
-- title:
--   OAI.SharpPlanar.diskAffine_mem_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.diskAffine_mem` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`, `open MeasureTheory Set`, `open scoped BigOperators`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma diskAffine_mem_e {j : ℕ} {w : ℂ} (hw : ‖w‖ ≤ 2) :
--       ‖diskAffine j w-(diskCenter j:ℂ)‖ ≤ 1/6
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.diskAffine` and `OAI.SharpPlanar.diskCenter` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.directMoment_piece_average_error_e`, `OAI.SharpPlanar.transformedIntegrand_analytic_e` and `OAI.SharpPlanar.transformedMoment_piece_average_error_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.diskAffine_mem)

import Mathlib
import Definitions.Def_OAIQ098E018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory Set

lemma diskAffine_mem_e {j : ℕ} {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖diskAffine j w-(diskCenter j:ℂ)‖ ≤ 1/6 := by
  sorry

end SharpPlanar

end OAI
end
