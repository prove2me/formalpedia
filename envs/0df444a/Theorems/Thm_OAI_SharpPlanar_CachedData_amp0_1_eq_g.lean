-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_amp0_1_eq_g
-- name    : OAI.SharpPlanar.CachedData.amp0_1_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T08:20:53.186908+00:00
-- url     : https://prove2.me/theorems/cfe8206a-3f7d-4597-8f3f-9b05d38eb8c4
-- title:
--   OAI.SharpPlanar.CachedData.amp0_1_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.amp0_1_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma amp0_1_eq_g (j : Fin 6) (i k : Fin 16) : amp0_1Expr j i k = amp0_1 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.amp0_1` and `OAI.SharpPlanar.CachedData.amp0_1Expr` (definitions bundle `OAIQ098G103` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.cm48_3_1_1.contains_g`, `OAI.SharpPlanar.CachedData.column24_1_contains_g`, `OAI.SharpPlanar.CachedData.column36_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U48.wuplus_column_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean (declaration OAI.SharpPlanar.CachedData.amp0_1_eq)

import Mathlib
import Definitions.Def_OAIQ098G103

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma amp0_1_eq_g (j : Fin 6) (i k : Fin 16) : amp0_1Expr j i k = amp0_1 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end
