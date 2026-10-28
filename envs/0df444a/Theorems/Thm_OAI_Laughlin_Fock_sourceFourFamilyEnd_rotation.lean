-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceFourFamilyEnd_rotation
-- name    : OAI.Laughlin.Fock.sourceFourFamilyEnd_rotation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:33:40.523873+00:00
-- url     : https://prove2.me/theorems/bfdd1df7-2d0d-4f8b-badb-5ae414c87a99
-- title:
--   OAI.Laughlin.Fock.sourceFourFamilyEnd_rotation: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceFourFamilyEnd_rotation` of [lean/OAI/Analysis/Laughlin/FourBody/FockCovariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/FockCovariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin`, `open scoped BigOperators Matrix Kronecker`):
--
--   ```lean
--   theorem sourceFourFamilyEnd_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
--       (i : FourWedgeIndex Q) (x : Space Q) :
--       sourceFourFamilyEnd Q i (exteriorRotation Q g x) =
--         ∑ j, fourBodySpinRepresentation Q g i j •
--           exteriorRotation Q g (sourceFourFamilyEnd Q j x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space`, `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Fock.exteriorRotation`, `OAI.Laughlin.Fock.sourceFourFamilyEnd`, `OAI.Laughlin.Spin.FourWedgeIndex` and `OAI.Laughlin.Spin.WedgePairIndex` (definitions bundle `OAIQ047L002` of this split); `OAI.Laughlin.Spin.fourBodySpinRepresentation` (definitions bundle `OAIQ047L004` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.fourCopyForm_allowance_identity`, `OAI.Laughlin.Fock.fourCopyForm_scaled_haar`, `OAI_Laughlin_Fock_physicalFourCopyEnd_cross_haar`, `OAI_Laughlin_Fock_sourceA4Form_retained` and `OAI.Laughlin.Fock.sourceA4Form_retained_bound` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/FockCovariance.lean (declaration OAI.Laughlin.Fock.sourceFourFamilyEnd_rotation)

import Mathlib
import Definitions.Def_OAIQ047L004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix Kronecker

theorem sourceFourFamilyEnd_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (i : FourWedgeIndex Q) (x : Space Q) :
    sourceFourFamilyEnd Q i (exteriorRotation Q g x) =
      ∑ j, fourBodySpinRepresentation Q g i j •
        exteriorRotation Q g (sourceFourFamilyEnd Q j x) := by
  sorry

end Laughlin.Fock

end OAI
end
