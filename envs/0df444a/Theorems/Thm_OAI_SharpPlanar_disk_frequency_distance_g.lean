-- Prove2me | Theorems.Thm_OAI_SharpPlanar_disk_frequency_distance_g
-- name    : OAI.SharpPlanar.disk_frequency_distance_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:14:58.770965+00:00
-- url     : https://prove2.me/theorems/dba76991-d050-462d-a835-c598a692c2db
-- title:
--   OAI.SharpPlanar.disk_frequency_distance_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.disk_frequency_distance` of [lean/OAI/Analysis/PlanarPacking/Cardinal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma disk_frequency_distance_g {j : ℕ} (hj : j < 6) {l : ℕ}
--       (hl : l ∈ Finset.Icc (j+1) 6) {t : ℂ}
--       (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖(l:ℂ)/6-t‖ ≤ 13/12
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.diskCenter` (definitions bundle `OAIQ098G072` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.complexU_disk_bound_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean (declaration OAI.SharpPlanar.disk_frequency_distance)

import Mathlib
import Definitions.Def_OAIQ098G072

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open MeasureTheory Set

lemma disk_frequency_distance_g {j : ℕ} (hj : j < 6) {l : ℕ}
    (hl : l ∈ Finset.Icc (j+1) 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖(l:ℂ)/6-t‖ ≤ 13/12 := by
  sorry

end SharpPlanar

end OAI
end
