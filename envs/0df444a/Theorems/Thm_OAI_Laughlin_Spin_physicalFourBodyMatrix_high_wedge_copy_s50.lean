-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_physicalFourBodyMatrix_high_wedge_copy_s50
-- name    : OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:57:09.754311+00:00
-- url     : https://prove2.me/theorems/549da007-8e97-4cd2-8518-dc2f00e30f4a
-- title:
--   OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy` of [lean/OAI/Analysis/Laughlin/FourBody/Support.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/Support.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open Rotation MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem physicalFourBodyMatrix_high_wedge_copy_s50 (Q r D : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
--       (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
--       (physicalFourBodyMatrix Q).map Complex.ofReal * fourWedgeInclusion Q r D hr hA hB = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Spin.genericCoupledWeight` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Spin.WedgePairIndex` and `OAI.Laughlin.Spin.physicalFourBodyMatrix` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Spin.fourWedgeInclusion` (definitions bundle `OAIQ050L016` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Spin.physicalFourBodyHaar_high_column_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/Support.lean (declaration OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy)

import Mathlib
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem physicalFourBodyMatrix_high_wedge_copy_s50 (Q r D : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    (physicalFourBodyMatrix Q).map Complex.ofReal * fourWedgeInclusion Q r D hr hA hB = 0 := by
  sorry

end Laughlin.Spin

end OAI
end
