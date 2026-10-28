-- Prove2me | Theorems.Thm_OAI_PlanarUnitDistances_IncidenceBand_choose
-- name    : OAI.PlanarUnitDistances.IncidenceBand.choose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T02:56:01.471774+00:00
-- url     : https://prove2.me/theorems/51f7e399-38af-44c9-b07e-a4a88dfd0638
-- title:
--   OAI.PlanarUnitDistances.IncidenceBand.choose: intermediate lemma from OpenAI, A power saving for planar unit distances
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarUnitDistances.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A power saving for planar unit distances*, OpenAI Math Release, September 23, 2026, result family 167, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarUnitDistances.IncidenceBand.choose` of [lean/OAI/Geometry/UnitDistances/UnitDistances/Tails.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/Tails.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarUnitDistances.IncidenceBand`, with `open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook`, `open scoped Classical`):
--
--   ```lean
--   theorem choose (s : Sequence) : ∃c : ℝ,0<c ∧ ∀δ : ℝ,0<δ →
--       ∃a : Params,∃b : ℝ,0<b ∧ ∀ᶠi in atTop,∃R : Realization s a i,∃J : ℝ,
--         c*scale s i/2≤J ∧ b≤event (WedgeLaw.law (graph s i)) (band R J δ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarUnitDistances.BudgetParameters.Params`, `OAI.PlanarUnitDistances.FiniteLaw.event`, `OAI.PlanarUnitDistances.GeometricLaw.Plane`, `OAI.PlanarUnitDistances.IncidenceBand.band`, `OAI.PlanarUnitDistances.IncidenceBook.Realization`, `OAI.PlanarUnitDistances.IncidenceScale.graph`, `OAI.PlanarUnitDistances.IncidenceScale.scale`, `OAI.PlanarUnitDistances.IncidenceSequence.Sequence` and `OAI.PlanarUnitDistances.WedgeLaw.law` (definitions bundle `OAIQ2Un000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarUnitDistances.main` of this split imports it.
-- source:
--   OpenAI, A power saving for planar unit distances, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/Tails.lean (declaration OAI.PlanarUnitDistances.IncidenceBand.choose)

import Mathlib
import Definitions.Def_OAIQ2Un000

section

attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceBand
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceRare IncidenceHeights ActualProfiles ProfileBudget BudgetParameters
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}

theorem choose (s : Sequence) : ∃c : ℝ,0<c ∧ ∀δ : ℝ,0<δ →
    ∃a : Params,∃b : ℝ,0<b ∧ ∀ᶠi in atTop,∃R : Realization s a i,∃J : ℝ,
      c*scale s i/2≤J ∧ b≤event (WedgeLaw.law (graph s i)) (band R J δ) := by
  sorry
end
end PlanarUnitDistances.IncidenceBand

end OAI
end
