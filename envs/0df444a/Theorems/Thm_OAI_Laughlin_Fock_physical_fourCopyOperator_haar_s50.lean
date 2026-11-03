-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_physical_fourCopyOperator_haar_s50
-- name    : OAI.Laughlin.Fock.physical_fourCopyOperator_haar_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:52:35.591253+00:00
-- url     : https://prove2.me/theorems/1a6f8d0a-c906-4a28-ab5f-5e44db1749f7
-- title:
--   OAI.Laughlin.Fock.physical_fourCopyOperator_haar_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.physical_fourCopyOperator_haar` of [lean/OAI/Analysis/Laughlin/FourBody/CopyOperatorHaar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/CopyOperatorHaar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem physical_fourCopyOperator_haar_s50 (Q D : ℕ) (hQ : D+2 ≤ Q)
--       (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
--       ((4*Q-1-2*D : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
--         (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
--           (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
--         (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Fock.contractionForm`, `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.OddPairLabel` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.occupationQuadratic`, `OAI.Laughlin.Fock.sourceFourFamilyEnd`, `OAI.Laughlin.Rotation.sourceHaar`, `OAI.Laughlin.Rotation.sourceSU2_measurableSpace`, `OAI.Laughlin.Spin.FourWedgeIndex`, `OAI.Laughlin.Spin.WedgePairIndex` and `OAI.Laughlin.Spin.oddPairDeficit` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.exteriorRotation`, `OAI.Laughlin.Fock.fourCopyOperator` and `OAI.Laughlin.Fock.physicalFourCopyEnd` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceA4Form_retained_bessel_bound_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/CopyOperatorHaar.lean (declaration OAI.Laughlin.Fock.physical_fourCopyOperator_haar)

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

theorem physical_fourCopyOperator_haar_s50 (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
    ((4*Q-1-2*D : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
        (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re := by
  sorry

end Laughlin.Fock

end OAI
end
