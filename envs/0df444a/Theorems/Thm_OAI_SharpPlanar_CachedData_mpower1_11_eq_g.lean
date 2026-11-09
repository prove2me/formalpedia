-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_11_eq_g
-- name    : OAI.SharpPlanar.CachedData.mpower1_11_eq_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:07:49.053215+00:00
-- url     : https://prove2.me/theorems/94b9d01f-5474-45bc-9636-894f07279892
-- title:
--   OAI.SharpPlanar.CachedData.mpower1_11_eq_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.mpower1_11_eq` of [lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers15.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers15.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma mpower1_11_eq_g (j : Fin 6) (i k : Fin 16) : mpower1_11Expr j i k = mpower1_11 j i k
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.CachedData.mpower1_11Expr` (definitions bundle `OAIQ098G1473` of this split); `OAI.SharpPlanar.CachedData.mpower1_11` (definitions bundle `OAIQ098G440` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein12.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein12.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein12.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein13.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein13.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein13.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein13.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein19.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein19.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein19.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein19.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein21.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein21.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein3.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein3.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hm1_1_1_11.contains_g` and `OAI.SharpPlanar.CachedData.mpower1_12_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers15.lean (declaration OAI.SharpPlanar.CachedData.mpower1_11_eq)

import Mathlib
import Definitions.Def_OAIQ098G1473

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma mpower1_11_eq_g (j : Fin 6) (i k : Fin 16) : mpower1_11Expr j i k = mpower1_11 j i k := by
  sorry
end SharpPlanar.CachedData

end OAI
end
