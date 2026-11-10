-- Prove2me | Theorems.Thm_OAI_SharpPlanar_piece_summand_bound_g
-- name    : OAI.SharpPlanar.piece_summand_bound_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T05:37:13.182209+00:00
-- url     : https://prove2.me/theorems/36584404-43be-42d6-a7b3-b01ee5b59648
-- title:
--   OAI.SharpPlanar.piece_summand_bound_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.piece_summand_bound` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerBasis`):
--
--   ```lean
--   lemma piece_summand_bound_g (x : X) (n : Node) (j : Fin 6) {t : ℝ}
--       (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
--       ‖(x (n,false):ℂ)*u n.val j.val t+(x (n,true):ℂ)*v n.val j.val t‖ ≤
--         densityCap j*(|x (n,false)|+|x (n,true)|)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` and `OAI.SharpPlanar.residues` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.X`, `OAI.SharpPlanar.u` and `OAI.SharpPlanar.v` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.IntegerBasis.densityCap` (definitions bundle `OAIQ098G365` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.piece_density_bound_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.piece_summand_bound)

import Mathlib
import Definitions.Def_OAIQ098G001
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

lemma piece_summand_bound_g (x : X) (n : Node) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖(x (n,false):ℂ)*u n.val j.val t+(x (n,true):ℂ)*v n.val j.val t‖ ≤
      densityCap j*(|x (n,false)|+|x (n,true)|) := by
  sorry

end SharpPlanar

end OAI
end
