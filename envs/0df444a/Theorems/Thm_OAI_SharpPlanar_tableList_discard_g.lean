-- Prove2me | Theorems.Thm_OAI_SharpPlanar_tableList_discard_g
-- name    : OAI.SharpPlanar.tableList_discard_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T03:42:27.889769+00:00
-- url     : https://prove2.me/theorems/cadb6472-2fdf-4a7d-89dc-07564426be8c
-- title:
--   OAI.SharpPlanar.tableList_discard_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.tableList_discard` of [lean/OAI/Analysis/PlanarPacking/Certificate/TableList.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableList.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Numerical`):
--
--   ```lean
--   lemma tableList_discard_g (a : Bool) : tableList a-IF (RF (tableList a))=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.X` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.L1Finite` (definitions bundle `OAIQ098G004` of this split); `OAI.SharpPlanar.Numerical.FiniteIndex` (definitions bundle `OAIQ098G007` of this split); `OAI.SharpPlanar.Numerical.IF` and `OAI.SharpPlanar.Numerical.RF` (definitions bundle `OAIQ098G010` of this split); `OAI.SharpPlanar.tableList` (definitions bundle `OAIQ098G1673` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.table_coeff_mass_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableList.lean (declaration OAI.SharpPlanar.tableList_discard)

import Mathlib
import Definitions.Def_OAIQ098G010
import Definitions.Def_OAIQ098G1673

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Numerical
lemma tableList_discard_g (a : Bool) : tableList a-IF (RF (tableList a))=0 := by
  sorry
end SharpPlanar

end OAI
end
