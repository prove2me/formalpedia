-- Prove2me | Theorems.Thm_OAI_SharpPlanar_kernelMoment_endpoint_bound_e
-- name    : OAI.SharpPlanar.kernelMoment_endpoint_bound_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T19:47:59.803704+00:00
-- url     : https://prove2.me/theorems/3e617a6b-95a6-40cd-86d8-443921ec01b7
-- title:
--   OAI.SharpPlanar.kernelMoment_endpoint_bound_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.kernelMoment_endpoint_bound` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerBasis`):
--
--   ```lean
--   lemma kernelMoment_endpoint_bound_e (j : Fin 7) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
--       ‖kernelMoment ell s ((j.val:ℝ)/6)‖ ≤
--         lambdaCap j*Real.exp (-Real.pi*dampingCap j*s)*(Real.pi*zCap j)^ell
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.kernelMoment` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.dampingCap`, `OAI.SharpPlanar.lambdaCap` and `OAI.SharpPlanar.zCap` (definitions bundle `OAIQ098E125` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.sharp_atomic_bound_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.kernelMoment_endpoint_bound)

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
open IntegerBasis

lemma kernelMoment_endpoint_bound_e (j : Fin 7) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖kernelMoment ell s ((j.val:ℝ)/6)‖ ≤
      lambdaCap j*Real.exp (-Real.pi*dampingCap j*s)*(Real.pi*zCap j)^ell := by
  sorry

end SharpPlanar

end OAI
end
