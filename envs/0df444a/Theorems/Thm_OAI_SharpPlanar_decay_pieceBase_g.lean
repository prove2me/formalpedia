-- Prove2me | Theorems.Thm_OAI_SharpPlanar_decay_pieceBase_g
-- name    : OAI.SharpPlanar.decay_pieceBase_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T20:50:33.419235+00:00
-- url     : https://prove2.me/theorems/b65a4f0f-8c89-463c-a72a-0a6ce5db49a0
-- title:
--   OAI.SharpPlanar.decay_pieceBase_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.decay_pieceBase` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerBasis`):
--
--   ```lean
--   lemma decay_pieceBase_g (j : Fin 6) (n : ℕ) :
--       Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*n) ≤ pieceBase j^n
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.dampingCap` and `OAI.SharpPlanar.pieceBase` (definitions bundle `OAIQ098G362` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.interpolation_exists_unique_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g`, `OAI.SharpPlanar.pieceL_le_intCap_g`, `OAI.SharpPlanar.rowTable_le_g` and `OAI.SharpPlanar.tail_second_bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.decay_pieceBase)

import Mathlib
import Definitions.Def_OAIQ098G362

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

lemma decay_pieceBase_g (j : Fin 6) (n : ℕ) :
    Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*n) ≤ pieceBase j^n := by
  sorry

end SharpPlanar

end OAI
end
