-- Prove2me | Theorems.Thm_OAI_SharpPlanar_sharp_integral_piece_bound_g
-- name    : OAI.SharpPlanar.sharp_integral_piece_bound_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T20:53:03.698787+00:00
-- url     : https://prove2.me/theorems/e814d250-d1a6-4f12-8f1b-eb7327e84f02
-- title:
--   OAI.SharpPlanar.sharp_integral_piece_bound_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.sharp_integral_piece_bound` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerBasis`):
--
--   ```lean
--   lemma sharp_integral_piece_bound_g (p : CardinalData) (j : Fin 6) (ell : ℕ) {s : ℝ}
--       (hs : 0 ≤ s) :
--       ‖∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, density p j.val t*kernelMoment ell s t‖ ≤
--         (|p.c₀|+|p.d₀|+‖p.x‖)*densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.CardinalData`, `OAI.SharpPlanar.X`, `OAI.SharpPlanar.density` and `OAI.SharpPlanar.kernelMoment` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.pieceL` and `OAI.SharpPlanar.zCap` (definitions bundle `OAIQ098G362` of this split); `OAI.SharpPlanar.IntegerBasis.densityCap` (definitions bundle `OAIQ098G365` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.sharp_moment_bound_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.sharp_integral_piece_bound)

import Mathlib
import Definitions.Def_OAIQ098G362
import Definitions.Def_OAIQ098G365

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

lemma sharp_integral_piece_bound_g (p : CardinalData) (j : Fin 6) (ell : ℕ) {s : ℝ}
    (hs : 0 ≤ s) :
    ‖∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, density p j.val t*kernelMoment ell s t‖ ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
  sorry

end SharpPlanar

end OAI
end
