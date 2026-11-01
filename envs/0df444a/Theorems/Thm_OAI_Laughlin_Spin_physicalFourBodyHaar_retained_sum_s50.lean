-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_physicalFourBodyHaar_retained_sum_s50
-- name    : OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T21:04:01.329232+00:00
-- url     : https://prove2.me/theorems/cc0af49d-9b5c-40d1-9d54-ce16fdfc0072
-- title:
--   OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum` of [lean/OAI/Analysis/Laughlin/FourBody/GlobalHaar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/GlobalHaar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open Rotation Fock`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem physicalFourBodyHaar_retained_sum_s50 (Q : ℕ) (hQ : 25 ≤ Q) :
--       matrixIntegral sourceHaar
--         (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) =
--       ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) •
--         fourCopyOperator Q (d.val+1) (by omega)
--           (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.OddPairLabel` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Rotation.conjugateOrbit` and `OAI.Laughlin.Rotation.matrixIntegral` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Spin.physicalFourError` (definitions bundle `OAIQ050L010` of this split); `OAI.Laughlin.Rotation.sourceHaar`, `OAI.Laughlin.Rotation.sourceSU2_measurableSpace`, `OAI.Laughlin.Spin.FourWedgeIndex`, `OAI.Laughlin.Spin.WedgePairIndex`, `OAI.Laughlin.Spin.oddPairDeficit` and `OAI.Laughlin.Spin.physicalFourBodyMatrix` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.fourCopyOperator` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Spin.fourBodySpinRepresentation` (definitions bundle `OAIQ050L024` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceA4Form_retained_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/GlobalHaar.lean (declaration OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum)

import Mathlib
import Definitions.Def_OAIQ050L024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation Fock
open scoped BigOperators Matrix

theorem physicalFourBodyHaar_retained_sum_s50 (Q : ℕ) (hQ : 25 ≤ Q) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) =
    ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) •
      fourCopyOperator Q (d.val+1) (by omega)
        (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s)) := by
  sorry

end Laughlin.Spin

end OAI
end
