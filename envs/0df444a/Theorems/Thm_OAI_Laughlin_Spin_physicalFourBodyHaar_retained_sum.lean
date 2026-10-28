-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_physicalFourBodyHaar_retained_sum
-- name    : OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:34:07.156022+00:00
-- url     : https://prove2.me/theorems/f0c2eb01-5bd5-40b8-b99d-0d150350f0ac
-- title:
--   OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum` of [lean/OAI/Analysis/Laughlin/FourBody/GlobalHaar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/GlobalHaar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open Rotation Fock`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem physicalFourBodyHaar_retained_sum (Q : ℕ) (hQ : 25 ≤ Q) :
--       matrixIntegral sourceHaar
--         (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) =
--       ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) •
--         fourCopyOperator Q (d.val+1) (by omega)
--           (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Rotation.SourceSU2`, `OAI.Laughlin.Spin.SpinIndex` and `OAI.Laughlin.Spin.physicalFourError` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Rotation.conjugateOrbit`, `OAI.Laughlin.Rotation.matrixIntegral`, `OAI.Laughlin.Spin.OddPairLabel` and `OAI.Laughlin.Spin.oddPairDeficit` (definitions bundle `OAIQ047L001` of this split); `OAI.Laughlin.Fock.fourCopyOperator`, `OAI.Laughlin.Rotation.sourceHaar`, `OAI.Laughlin.Rotation.sourceSU2_measurableSpace`, `OAI.Laughlin.Spin.FourWedgeIndex`, `OAI.Laughlin.Spin.WedgePairIndex` and `OAI.Laughlin.Spin.physicalFourBodyMatrix` (definitions bundle `OAIQ047L002` of this split); `OAI.Laughlin.Spin.fourBodySpinRepresentation` (definitions bundle `OAIQ047L004` of this split).
--
--   **Used by.** The proofs of `OAI_Laughlin_Fock_sourceA4Form_retained` and `OAI.Laughlin.Fock.sourceA4Form_retained_bound` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/GlobalHaar.lean (declaration OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum)

import Mathlib
import Definitions.Def_OAIQ047L004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation Fock
open scoped BigOperators Matrix

theorem physicalFourBodyHaar_retained_sum (Q : ℕ) (hQ : 25 ≤ Q) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) =
    ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) •
      fourCopyOperator Q (d.val+1) (by omega)
        (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s)) := by
  sorry

end Laughlin.Spin

end OAI
end
