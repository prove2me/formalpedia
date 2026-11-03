-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_complexThreeGram_sub_one_spectral_s50
-- name    : OAI.Laughlin.Fock.complexThreeGram_sub_one_spectral_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:49:36.662218+00:00
-- url     : https://prove2.me/theorems/c9cc17d7-01c3-4f62-a742-89fd7cb77740
-- title:
--   OAI.Laughlin.Fock.complexThreeGram_sub_one_spectral_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.complexThreeGram_sub_one_spectral` of [lean/OAI/Analysis/Laughlin/ThreeBody/FockBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/FockBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin MeasureTheory Filter`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem complexThreeGram_sub_one_spectral_s50 (Q : ℕ) (hQ : 2 ≤ Q) :
--       complexThreeGram Q-1 = ∑ z : Fin (Q+1), (gramEigenvalueFormula Q z.val : ℂ) •
--         (threeSpinProjector Q hQ z).map Complex.ofReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.Orbital` (definitions bundle `OAIQ050L003` of this split); `OAI.Laughlin.gramEigenvalueFormula` (definitions bundle `OAIQ050L008` of this split); `OAI.Laughlin.Fock.complexThreeGram` and `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Spin.threeSpinProjector` (definitions bundle `OAIQ050L016` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physical_fock_sharp_budget_eventually_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/FockBudget.lean (declaration OAI.Laughlin.Fock.complexThreeGram_sub_one_spectral)

import Mathlib
import Definitions.Def_OAIQ050L008
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory Filter
open scoped BigOperators Matrix

theorem complexThreeGram_sub_one_spectral_s50 (Q : ℕ) (hQ : 2 ≤ Q) :
    complexThreeGram Q-1 = ∑ z : Fin (Q+1), (gramEigenvalueFormula Q z.val : ℂ) •
      (threeSpinProjector Q hQ z).map Complex.ofReal := by
  sorry

end Laughlin.Fock

end OAI
end
