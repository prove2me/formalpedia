-- Prove2me | Theorems.Thm_OAI_SharpPlanar_sharp_S_tail_g
-- name    : OAI.SharpPlanar.sharp_S_tail_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T20:55:11.100133+00:00
-- url     : https://prove2.me/theorems/03f4075f-5a6e-4363-aac9-97ec832d48b3
-- title:
--   OAI.SharpPlanar.sharp_S_tail_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.sharp_S_tail` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerBasis`):
--
--   ```lean
--   theorem sharp_S_tail_g (x : X) (N : ℕ) : rowTailNorm (S x) N ≤ rowTable N*‖x‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.X` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.S` (definitions bundle `OAIQ098G004` of this split); `OAI.SharpPlanar.rowTailNorm` (definitions bundle `OAIQ098G362` of this split); `OAI.SharpPlanar.rowTable` (definitions bundle `OAIQ098G379` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.exterior_exterior_norm_g` and `OAI.SharpPlanar.Numerical.finiteA_bijective_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.sharp_S_tail)

import Mathlib
import Definitions.Def_OAIQ098G379

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

theorem sharp_S_tail_g (x : X) (N : ℕ) : rowTailNorm (S x) N ≤ rowTable N*‖x‖ := by
  sorry

end SharpPlanar

end OAI
end
