-- Prove2me | Theorems.Thm_OAI_SharpPlanar_endpoint_kernel_bounds_e
-- name    : OAI.SharpPlanar.endpoint_kernel_bounds_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T19:47:55.452812+00:00
-- url     : https://prove2.me/theorems/ea997a6d-50f9-4a19-8e2b-368bf1e54e23
-- title:
--   OAI.SharpPlanar.endpoint_kernel_bounds_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.endpoint_kernel_bounds` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`):
--
--   ```lean
--   lemma endpoint_kernel_bounds_e (j : Fin 7) :
--       ‖lambda ((j.val:ℝ)/6)‖ ≤ lambdaCap j ∧
--       ‖z ((j.val:ℝ)/6)‖ ≤ zCap j ∧
--       dampingCap j ≤ (z ((j.val:ℝ)/6)).im
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.lambda` and `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.dampingCap`, `OAI.SharpPlanar.lambdaCap` and `OAI.SharpPlanar.zCap` (definitions bundle `OAIQ098E125` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.kernelMoment_endpoint_bound_e`, `OAI.SharpPlanar.piece_damping_bound_e` and `OAI.SharpPlanar.piece_kernel_bounds_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.endpoint_kernel_bounds)

import Mathlib
import Definitions.Def_OAIQ098E125

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma endpoint_kernel_bounds_e (j : Fin 7) :
    ‖lambda ((j.val:ℝ)/6)‖ ≤ lambdaCap j ∧
    ‖z ((j.val:ℝ)/6)‖ ≤ zCap j ∧
    dampingCap j ≤ (z ((j.val:ℝ)/6)).im := by
  sorry

end SharpPlanar

end OAI
end
