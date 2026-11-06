-- Prove2me | Theorems.Thm_OAI_SharpPlanar_tableCoords_mem_e
-- name    : OAI.SharpPlanar.tableCoords_mem_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:50:32.811409+00:00
-- url     : https://prove2.me/theorems/e2660b75-af72-4443-b222-c142b5a4ce5b
-- title:
--   OAI.SharpPlanar.tableCoords_mem_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.tableCoords_mem` of [lean/OAI/Analysis/PlanarPacking/Certificate/TableList.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableList.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Numerical`):
--
--   ```lean
--   lemma tableCoords_mem_e (a : Bool) : Memℓp (tableCoords a) 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098E000` of this split); `OAI.SharpPlanar.tableCoords` (definitions bundle `OAIQ098E015` of this split).
--
--   **Used by.** The definitions bundle `OAIQ098E239` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableList.lean (declaration OAI.SharpPlanar.tableCoords_mem)

import Mathlib
import Definitions.Def_OAIQ098E015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Numerical
lemma tableCoords_mem_e (a : Bool) : Memℓp (tableCoords a) 1 := by
  sorry
end SharpPlanar

end OAI
end
