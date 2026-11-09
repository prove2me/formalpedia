-- Prove2me | Theorems.Thm_OAI_SharpPlanar_tableData_density_g
-- name    : OAI.SharpPlanar.tableData_density_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T05:43:20.480915+00:00
-- url     : https://prove2.me/theorems/5ac75252-5318-4bf7-af70-19fce4f9b8da
-- title:
--   OAI.SharpPlanar.tableData_density_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.tableData_density` of [lean/OAI/Analysis/PlanarPacking/TableDensityBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableDensityBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   lemma tableData_density_g (a : Bool) (j : ℕ) (t : ℝ) :
--       density (tableData a) j t = tableDensity a j t
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.density` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.tableDensity` (definitions bundle `OAIQ098G1681` of this split); `OAI.SharpPlanar.tableData` (definitions bundle `OAIQ098G1691` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.fullMoment_direct_g` and `OAI.SharpPlanar.tableMomentK_eq_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableDensityBridge.lean (declaration OAI.SharpPlanar.tableData_density)

import Mathlib
import Definitions.Def_OAIQ098G1681
import Definitions.Def_OAIQ098G1691

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma tableData_density_g (a : Bool) (j : ℕ) (t : ℝ) :
    density (tableData a) j t = tableDensity a j t := by
  sorry
end SharpPlanar

end OAI
end
