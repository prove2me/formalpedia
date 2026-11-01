-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_physicalFourCopyEnd_column_s50
-- name    : OAI.Laughlin.Fock.physicalFourCopyEnd_column_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:51:35.752649+00:00
-- url     : https://prove2.me/theorems/894c5eac-ea3e-49a8-ab06-06ec21bb4917
-- title:
--   OAI.Laughlin.Fock.physicalFourCopyEnd_column_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.physicalFourCopyEnd_column` of [lean/OAI/Analysis/Laughlin/FourBody/HighestFock.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/HighestFock.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem physicalFourCopyEnd_column_s50 (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) (x : Space Q) :
--       (∑ i, star (retainedFourInclusion Q D hQ r i 0) • sourceFourFamilyEnd Q i x) =
--         physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Spin.OddPairLabel` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.fourSpinWeight` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.sourceFourFamilyEnd`, `OAI.Laughlin.Spin.FourWedgeIndex`, `OAI.Laughlin.Spin.WedgePairIndex` and `OAI.Laughlin.Spin.oddPairDeficit` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.physicalFourCopyEnd` and `OAI.Laughlin.Spin.retainedFourInclusion` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physicalFourCopyEnd_cross_haar_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/HighestFock.lean (declaration OAI.Laughlin.Fock.physicalFourCopyEnd_column)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physicalFourCopyEnd_column_s50 (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) (x : Space Q) :
    (∑ i, star (retainedFourInclusion Q D hQ r i 0) • sourceFourFamilyEnd Q i x) =
      physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) x := by
  sorry

end Laughlin.Fock

end OAI
end
