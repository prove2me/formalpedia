-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_fourBody_haar_compressed_s50
-- name    : OAI.Laughlin.Spin.fourBody_haar_compressed_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T21:02:55.776446+00:00
-- url     : https://prove2.me/theorems/5fb408e2-8c06-4724-9b87-0a1da10695ee
-- title:
--   OAI.Laughlin.Spin.fourBody_haar_compressed_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.fourBody_haar_compressed` of [lean/OAI/Analysis/Laughlin/FourBody/MultiplicityHaar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/MultiplicityHaar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open Rotation MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem fourBody_haar_compressed_s50 (Q D E : ℕ) (hD : D+2 ≤ Q) (hE : E+2 ≤ Q)
--       (r : OddPairLabel D) (s : OddPairLabel E) (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
--       (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
--         (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s =
--       rectangularIntegral sourceHaar (rectangularOrbit
--         (sourceSpinRepresentation (fourSpinWeight Q D)) (sourceSpinRepresentation (fourSpinWeight Q E))
--         ((retainedFourInclusion Q D hD r)ᴴ * M * retainedFourInclusion Q E hE s))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.OddPairLabel` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Rotation.conjugateOrbit`, `OAI.Laughlin.Rotation.matrixIntegral` and `OAI.Laughlin.Spin.fourSpinWeight` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Rotation.rectangularIntegral` and `OAI.Laughlin.Rotation.rectangularOrbit` (definitions bundle `OAIQ050L008` of this split); `OAI.Laughlin.Rotation.sourceHaar`, `OAI.Laughlin.Rotation.sourceSU2_measurableSpace`, `OAI.Laughlin.Spin.FourWedgeIndex` and `OAI.Laughlin.Spin.WedgePairIndex` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Rotation.sourceSpinRepresentation` and `OAI.Laughlin.Spin.retainedFourInclusion` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Spin.fourBodySpinRepresentation` (definitions bundle `OAIQ050L024` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Spin.fourBody_haar_unequal_spin_s50` and `OAI.Laughlin.Spin.physical_fourBody_haar_multiplicity_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/MultiplicityHaar.lean (declaration OAI.Laughlin.Spin.fourBody_haar_compressed)

import Mathlib
import Definitions.Def_OAIQ050L024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem fourBody_haar_compressed_s50 (Q D E : ℕ) (hD : D+2 ≤ Q) (hE : E+2 ≤ Q)
    (r : OddPairLabel D) (s : OddPairLabel E) (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s =
    rectangularIntegral sourceHaar (rectangularOrbit
      (sourceSpinRepresentation (fourSpinWeight Q D)) (sourceSpinRepresentation (fourSpinWeight Q E))
      ((retainedFourInclusion Q D hD r)ᴴ * M * retainedFourInclusion Q E hE s)) := by
  sorry

end Laughlin.Spin

end OAI
end
