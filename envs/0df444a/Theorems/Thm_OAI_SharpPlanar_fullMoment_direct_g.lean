-- Prove2me | Theorems.Thm_OAI_SharpPlanar_fullMoment_direct_g
-- name    : OAI.SharpPlanar.fullMoment_direct_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T05:39:58.818798+00:00
-- url     : https://prove2.me/theorems/46ac4d7c-5a50-46fc-abfd-2d9d1d04e777
-- title:
--   OAI.SharpPlanar.fullMoment_direct_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.fullMoment_direct` of [lean/OAI/Analysis/PlanarPacking/FullMomentBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FullMomentBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   lemma fullMoment_direct_g (a : Bool) (m : ℝ) (ell : ℕ) :
--       fullMoment a false m ell=cardinalSeries (tableData a) ell m/(ell.factorial:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.cardinalSeries` (definitions bundle `OAIQ098G1642` of this split); `OAI.SharpPlanar.fullMoment` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.tableData` (definitions bundle `OAIQ098G1691` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.exactLeft_origin_positive_g`, `OAI.SharpPlanar.halfSign_0_N1_right_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g`, `OAI.SharpPlanar.normalizedH_table_g` and `OAI.sharp_fourier_certificate` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FullMomentBridge.lean (declaration OAI.SharpPlanar.fullMoment_direct)

import Mathlib
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1682
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
lemma fullMoment_direct_g (a : Bool) (m : ℝ) (ell : ℕ) :
    fullMoment a false m ell=cardinalSeries (tableData a) ell m/(ell.factorial:ℝ) := by
  sorry
end SharpPlanar

end OAI
end
