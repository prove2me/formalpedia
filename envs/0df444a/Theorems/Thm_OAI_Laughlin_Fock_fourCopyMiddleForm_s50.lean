-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_fourCopyMiddleForm_s50
-- name    : OAI.Laughlin.Fock.fourCopyMiddleForm_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:50:33.651681+00:00
-- url     : https://prove2.me/theorems/6c0258fe-c2eb-4c9c-a448-5d47e1ab2fb9
-- title:
--   OAI.Laughlin.Fock.fourCopyMiddleForm_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.fourCopyMiddleForm` of [lean/OAI/Analysis/Laughlin/FourBody/MiddleForm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/MiddleForm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Spin`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem fourCopyMiddleForm_s50 (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) (x : Space Q) :
--       (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
--         (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ (finiteFourMiddle Q D)) x).re =
--       (contractionForm Q (sourceFourFamilyEnd Q)
--         (retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
--           (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ) x).re +
--       (3/10^6 : ℝ) * (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
--         (∑ r : OddPairLabel D, (contractionForm Q (sourceFourFamilyEnd Q)
--           (retainedFourInclusion Q D hQ r*(retainedFourInclusion Q D hQ r)ᴴ) x).re) -
--       (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
--         (contractionForm Q (sourceFourFamilyEnd Q)
--           (fourCopyOperator Q D hQ (fun r s => physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s))) x).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Fock.contractionForm`, `OAI.Laughlin.Fock.firstOddPairLabel` and `OAI.Laughlin.Spin.OddPairLabel` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.fourSpinWeight` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.finiteFourMiddle` and `OAI.Laughlin.Spin.physicalFourError` (definitions bundle `OAIQ050L010` of this split); `OAI.Laughlin.Fock.sourceFourFamilyEnd`, `OAI.Laughlin.Spin.FourWedgeIndex`, `OAI.Laughlin.Spin.WedgePairIndex` and `OAI.Laughlin.Spin.oddPairDeficit` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.fourCopyOperator` and `OAI.Laughlin.Spin.retainedFourInclusion` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceA4Form_retained_bessel_bound_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/MiddleForm.lean (declaration OAI.Laughlin.Fock.fourCopyMiddleForm)

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
open Spin
open scoped BigOperators Matrix

theorem fourCopyMiddleForm_s50 (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ (finiteFourMiddle Q D)) x).re =
    (contractionForm Q (sourceFourFamilyEnd Q)
      (retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
        (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ) x).re +
    (3/10^6 : ℝ) * (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (∑ r : OddPairLabel D, (contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r*(retainedFourInclusion Q D hQ r)ᴴ) x).re) -
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q)
        (fourCopyOperator Q D hQ (fun r s => physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s))) x).re := by
  sorry

end Laughlin.Fock

end OAI
end
