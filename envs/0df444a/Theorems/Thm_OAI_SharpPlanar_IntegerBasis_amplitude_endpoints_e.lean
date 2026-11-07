-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerBasis_amplitude_endpoints_e
-- name    : OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T20:38:52.35598+00:00
-- url     : https://prove2.me/theorems/c976f846-f72f-4e14-8d7a-e0264bf28f61
-- title:
--   OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerBasis.amplitude_endpoints` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerBasis`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerIntervals IntegerAlpha`):
--
--   ```lean
--   lemma amplitude_endpoints_e (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) :
--       ‖uAmplitude n j.val ((j.val:ℝ)/6)‖ ≤ densityCap j ∧
--       ‖uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ ≤ densityCap j ∧
--       ‖vAmplitude n j.val‖ ≤ densityCap j
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.residues` (definitions bundle `OAIQ098E000` of this split); `OAI.SharpPlanar.IntegerBasis.vAmplitude` (definitions bundle `OAIQ098E087` of this split); `OAI.SharpPlanar.IntegerBasis.uAmplitude` (definitions bundle `OAIQ098E111` of this split); `OAI.SharpPlanar.IntegerBasis.densityCap` (definitions bundle `OAIQ098E126` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerBasis.basis_density_bounds_e` and `OAI.SharpPlanar.IntegerBasis.uAmplitude_bound_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.IntegerBasis.amplitude_endpoints)

import Mathlib
import Definitions.Def_OAIQ098E126

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma amplitude_endpoints_e (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) :
    ‖uAmplitude n j.val ((j.val:ℝ)/6)‖ ≤ densityCap j ∧
    ‖uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ ≤ densityCap j ∧
    ‖vAmplitude n j.val‖ ≤ densityCap j := by
  sorry

end SharpPlanar.IntegerBasis

end OAI
end
