-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_fourCopyForm_scaled_haar
-- name    : OAI.Laughlin.Fock.fourCopyForm_scaled_haar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:29:42.875781+00:00
-- url     : https://prove2.me/theorems/c16a5d0d-0ff3-4475-97b0-3ed58d55e6c3
-- title:
--   OAI.Laughlin.Fock.fourCopyForm_scaled_haar: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.fourCopyForm_scaled_haar` of [lean/OAI/Analysis/Laughlin/FourBody/RetainedComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/RetainedComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Spin Rotation MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem fourCopyForm_scaled_haar (Q D : ℕ) (hQ : D+2 ≤ Q)
--       (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
--       (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
--         (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re =
--       ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
--         (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
--           (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space`, `OAI.Laughlin.Fock.contractionForm`, `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Spin.OddPairLabel` and `OAI.Laughlin.Spin.oddPairDeficit` (definitions bundle `OAIQ047L001` of this split); `OAI.Laughlin.Fock.exteriorRotation`, `OAI.Laughlin.Fock.fourCopyOperator`, `OAI.Laughlin.Fock.occupationQuadratic`, `OAI.Laughlin.Fock.physicalFourCopyEnd`, `OAI.Laughlin.Fock.sourceFourFamilyEnd`, `OAI.Laughlin.Rotation.sourceHaar`, `OAI.Laughlin.Rotation.sourceSU2_measurableSpace`, `OAI.Laughlin.Spin.FourWedgeIndex` and `OAI.Laughlin.Spin.WedgePairIndex` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceA4Form_retained_bound` of this split imports it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/RetainedComparison.lean (declaration OAI.Laughlin.Fock.fourCopyForm_scaled_haar)

import Mathlib
import Definitions.Def_OAIQ047L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

theorem fourCopyForm_scaled_haar (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re =
    ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
        (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  sorry

end Laughlin.Fock

end OAI
end
