-- Prove2me | Theorems.Thm_OAI_SharpPlanar_scaled_table_basis_g
-- name    : OAI.SharpPlanar.scaled_table_basis_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T17:18:46.073692+00:00
-- url     : https://prove2.me/theorems/6d2461a6-e1fa-4626-b859-4e1f51ae516b
-- title:
--   OAI.SharpPlanar.scaled_table_basis_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.scaled_table_basis` of [lean/OAI/Analysis/PlanarPacking/TableDensityBase.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableDensityBase.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerIntervals IntegerBasis IntegerGrid`, `open scoped BigOperators`):
--
--   ```lean
--   lemma scaled_table_basis_g {a : CBox} {n j : ℕ} {w t : ℝ} {d : Bool}
--       (ha : a.Contains ((w:ℂ)*basisFunction d n j t)) (i : Bool) :
--       (a.scale (tableNum i d n) 10000000000).Contains
--         (((if d then (tableD i n:ℝ) else (tableC i n:ℝ)):ℂ)*((w:ℂ)*basisFunction d n j t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.tableC` and `OAI.SharpPlanar.tableD` (definitions bundle `OAIQ098G015` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox` and `OAI.SharpPlanar.IntegerIntervals.CBox.scale` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerBasis.basisFunction` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.tableNum` (definitions bundle `OAIQ098G396` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.tableTerm100_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm13_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm15_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm16_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm19_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm1_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm21_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm24_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm25_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm27_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm28_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm31_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm33_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm36_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm37_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm39_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm3_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm40_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm45_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm48_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm49_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm4_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm55_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm57_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm61_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm63_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm64_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm69_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm72_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm73_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm79_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm7_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm81_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm85_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm87_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm88_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm93_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm96_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm97_contains_g` and `OAI.SharpPlanar.CachedData.tableTerm9_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableDensityBase.lean (declaration OAI.SharpPlanar.scaled_table_basis)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G396

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
open scoped BigOperators

lemma scaled_table_basis_g {a : CBox} {n j : ℕ} {w t : ℝ} {d : Bool}
    (ha : a.Contains ((w:ℂ)*basisFunction d n j t)) (i : Bool) :
    (a.scale (tableNum i d n) 10000000000).Contains
      (((if d then (tableD i n:ℝ) else (tableC i n:ℝ)):ℂ)*((w:ℂ)*basisFunction d n j t)) := by
  sorry

end SharpPlanar

end OAI
end
