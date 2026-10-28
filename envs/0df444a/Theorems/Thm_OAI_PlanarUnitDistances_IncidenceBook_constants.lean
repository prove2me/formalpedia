-- Prove2me | Theorems.Thm_OAI_PlanarUnitDistances_IncidenceBook_constants
-- name    : OAI.PlanarUnitDistances.IncidenceBook.constants
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T02:57:14.149966+00:00
-- url     : https://prove2.me/theorems/d867e032-502c-4761-bcc9-49be872b38b3
-- title:
--   OAI.PlanarUnitDistances.IncidenceBook.constants: intermediate lemma from OpenAI, A power saving for planar unit distances
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarUnitDistances.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A power saving for planar unit distances*, OpenAI Math Release, September 23, 2026, result family 167, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarUnitDistances.IncidenceBook.constants` of [lean/OAI/Geometry/UnitDistances/UnitDistances/Profiles.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/Profiles.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarUnitDistances.IncidenceBook`, with `open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook`, `open scoped Classical`):
--
--   ```lean
--   theorem constants (s : Sequence) :
--       ∃s₀ C L : ℝ,0 < s₀ ∧ 0 < C ∧ 0 < L ∧
--         ∀a : Params,2*a.epsilon ≤ s₀ → ∀ᶠi in atTop,∃R : Realization s a i,R.Valid C L
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarUnitDistances.BudgetParameters.Params`, `OAI.PlanarUnitDistances.IncidenceBook.Realization`, `OAI.PlanarUnitDistances.IncidenceSequence.Sequence` and `OAI.PlanarUnitDistances.IncidenceBook.Realization.Valid` (definitions bundle `OAIQ2Un000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarUnitDistances.IncidenceBand.choose` of this split imports it.
-- source:
--   OpenAI, A power saving for planar unit distances, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/Profiles.lean (declaration OAI.PlanarUnitDistances.IncidenceBook.constants)

import Mathlib
import Definitions.Def_OAIQ2Un000

section

attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceBook
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale ActualScoreBook LevelSnapshot BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params) (i : ℕ)

variable {s a i}

theorem constants (s : Sequence) :
    ∃s₀ C L : ℝ,0 < s₀ ∧ 0 < C ∧ 0 < L ∧
      ∀a : Params,2*a.epsilon ≤ s₀ → ∀ᶠi in atTop,∃R : Realization s a i,R.Valid C L := by
  sorry
end
end PlanarUnitDistances.IncidenceBook

end OAI
end
