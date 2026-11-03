-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_fourBody_cross_orbit_s50
-- name    : OAI.Laughlin.Spin.fourBody_cross_orbit_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T21:02:45.060602+00:00
-- url     : https://prove2.me/theorems/17ada544-f1f5-4f3d-bd8a-59e22db5b9ca
-- title:
--   OAI.Laughlin.Spin.fourBody_cross_orbit_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.fourBody_cross_orbit` of [lean/OAI/Analysis/Laughlin/FourBody/MultiplicityHaar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/MultiplicityHaar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open Rotation MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem fourBody_cross_orbit_s50 (Q D : ℕ) (hD : D+2 ≤ Q) (r s : OddPairLabel D)
--       (M : Matrix (Fin (fourSpinWeight Q D+1)) (Fin (fourSpinWeight Q D+1)) ℂ) :
--       matrixIntegral sourceHaar (conjugateOrbit (fourBodySpinRepresentation Q)
--         (retainedFourInclusion Q D hD r * M * (retainedFourInclusion Q D hD s)ᴴ)) =
--         (Matrix.trace M / (4*Q-1-2*D : ℕ)) •
--           (retainedFourInclusion Q D hD r * (retainedFourInclusion Q D hD s)ᴴ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.OddPairLabel` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Rotation.conjugateOrbit`, `OAI.Laughlin.Rotation.matrixIntegral` and `OAI.Laughlin.Spin.fourSpinWeight` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Rotation.sourceHaar`, `OAI.Laughlin.Rotation.sourceSU2_measurableSpace`, `OAI.Laughlin.Spin.FourWedgeIndex` and `OAI.Laughlin.Spin.WedgePairIndex` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Spin.retainedFourInclusion` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Spin.fourBodySpinRepresentation` (definitions bundle `OAIQ050L024` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physicalFourCopyEnd_cross_haar_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/MultiplicityHaar.lean (declaration OAI.Laughlin.Spin.fourBody_cross_orbit)

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

theorem fourBody_cross_orbit_s50 (Q D : ℕ) (hD : D+2 ≤ Q) (r s : OddPairLabel D)
    (M : Matrix (Fin (fourSpinWeight Q D+1)) (Fin (fourSpinWeight Q D+1)) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (fourBodySpinRepresentation Q)
      (retainedFourInclusion Q D hD r * M * (retainedFourInclusion Q D hD s)ᴴ)) =
      (Matrix.trace M / (4*Q-1-2*D : ℕ)) •
        (retainedFourInclusion Q D hD r * (retainedFourInclusion Q D hD s)ᴴ) := by
  sorry

end Laughlin.Spin

end OAI
end
