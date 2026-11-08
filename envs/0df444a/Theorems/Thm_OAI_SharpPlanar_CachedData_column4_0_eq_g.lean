-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_column4_0_eq_g
-- name    : OAI.SharpPlanar.CachedData.column4_0_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T20:06:15.05077+00:00
-- url     : https://prove2.me/theorems/55e7e579-7ec7-49fd-a373-9b444c648ca1
-- title:
--   OAI.SharpPlanar.CachedData.column4_0_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.column4_0_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma column4_0_eq_g (j : Fin 6) (i k : Fin 16) : column4_0Expr j i k = column4_0 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.column4_0` (definitions bundle `OAIQ098G038` of this split); `OAI.SharpPlanar.CachedData.column4_0Expr` (definitions bundle `OAIQ098G058` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.cm4_4_0_0.contains_g`, `OAI.SharpPlanar.CachedData.tableTerm4_contains_g`, `OAI.SharpPlanar.Numerical.Lmat_column_g`, `OAI.SharpPlanar.Numerical.defectminus_column_g`, `OAI.SharpPlanar.Numerical.defectplus_column_g`, `OAI.SharpPlanar.Numerical.dentry2_2_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_g` and `OAI.SharpPlanar.Numerical.lentry8_2_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean (declaration OAI.SharpPlanar.CachedData.column4_0_eq)

import Mathlib
import Definitions.Def_OAIQ098G038
import Definitions.Def_OAIQ098G058

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column4_0_eq_g (j : Fin 6) (i k : Fin 16) : column4_0Expr j i k = column4_0 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end
