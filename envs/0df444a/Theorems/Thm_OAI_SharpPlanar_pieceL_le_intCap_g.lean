-- Prove2me | Theorems.Thm_OAI_SharpPlanar_pieceL_le_intCap_g
-- name    : OAI.SharpPlanar.pieceL_le_intCap_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T20:54:55.249207+00:00
-- url     : https://prove2.me/theorems/0dcfd8ac-0213-462d-b8e4-62b8bb3f45d8
-- title:
--   OAI.SharpPlanar.pieceL_le_intCap_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.pieceL_le_intCap` of [lean/OAI/Analysis/PlanarPacking/RationalBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/RationalBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerBasis`, `open scoped BigOperators`):
--
--   ```lean
--   lemma pieceL_le_intCap_g (j : Fin 6) (n : ℕ) : pieceL j n ≤ pieceIntCap j n
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.pieceIntCap` (definitions bundle `OAIQ098G1670` of this split); `OAI.SharpPlanar.pieceL` (definitions bundle `OAIQ098G362` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.transformEnvelope_le_rat_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/RationalBounds.lean (declaration OAI.SharpPlanar.pieceL_le_intCap)

import Mathlib
import Definitions.Def_OAIQ098G1670

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma pieceL_le_intCap_g (j : Fin 6) (n : ℕ) : pieceL j n ≤ pieceIntCap j n := by
  sorry
end SharpPlanar

end OAI
end
