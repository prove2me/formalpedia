-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_cover_check_g
-- name    : OAI.SharpPlanar.Numerical.finiteIndex_cover_check_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:08:43.725207+00:00
-- url     : https://prove2.me/theorems/83f0e8e3-519e-483d-94c8-0d9d464a8f43
-- title:
--   OAI.SharpPlanar.Numerical.finiteIndex_cover_check_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.finiteIndex_cover_check` of [lean/OAI/Analysis/PlanarPacking/Indices.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma finiteIndex_cover_check_g : ∀ n : Fin 101, 0<n.val ∧ n.val%12∈residues → ∀ d : Bool,
--       ∃ i : FiniteIndex, (finiteIndex i).1.val=n.val ∧ (finiteIndex i).2=d
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` and `OAI.SharpPlanar.residues` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.Numerical.FiniteIndex` and `OAI.SharpPlanar.Numerical.finiteIndex` (definitions bundle `OAIQ098G007` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Numerical.finiteIndex_range_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean (declaration OAI.SharpPlanar.Numerical.finiteIndex_cover_check)

import Mathlib
import Definitions.Def_OAIQ098G007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma finiteIndex_cover_check_g : ∀ n : Fin 101, 0<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : FiniteIndex, (finiteIndex i).1.val=n.val ∧ (finiteIndex i).2=d := by
  sorry
end SharpPlanar.Numerical

end OAI
end
