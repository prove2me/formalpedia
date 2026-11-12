-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Foundations_Repetition_selected_coordinate_probability_le_value_add_error
-- name    : OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:47:43.688258+00:00
-- url     : https://prove2.me/theorems/a13eafa7-40b3-4b57-87d7-1fe10dbb33fc
-- title:
--   OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error` of [lean/OAI/Computability/UniqueGames/Games/CompletedSamplingLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Games/CompletedSamplingLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Foundations.Repetition`, with `open scoped BigOperators`, `open Games`):
--
--   ```lean
--   theorem selected_coordinate_probability_le_value_add_error
--       (G : Game Q₁ Q₂ A₁ A₂)
--       (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
--       (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
--       (j : {i : Fin n // i ∉ selected}) :
--       ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
--         (G.coordinateWin strategy j.1) ≤
--           G.value + selectedEmbeddingError G strategy selected positive j
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Foundations.Games.Game`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` and `OAI.UniqueGamesTheorem.Foundations.Games.Game.repetition` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Foundations.Games.Strategy` (definitions bundle `OAIQ252P001` of this split); `OAI.UniqueGamesTheorem.Foundations.Games.Game.coordinateWin`, `OAI.UniqueGamesTheorem.Foundations.Games.Game.selectedSuccess` and `OAI.UniqueGamesTheorem.Foundations.Games.Game.selectedWins` (definitions bundle `OAIQ252P003` of this split); `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.condition` (definitions bundle `OAIQ252P006` of this split); `OAI.UniqueGamesTheorem.Foundations.Repetition.selectedEmbeddingError` and `OAI.UniqueGamesTheorem.Foundations.Games.Game.value` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proofs of `OAI.PerfectCompleteness.OddListGame.repetition_halfRate` and `OAI.PerfectCompleteness.SourceOddLists.repetition_halfRate` of this split import it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Games/CompletedSamplingLemmas.lean (declaration OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error)

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std
import Definitions.Def_OAIQ252P011

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_coordinate_probability_le_value_add_error
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
      (G.coordinateWin strategy j.1) ≤
        G.value + selectedEmbeddingError G strategy selected positive j := by
  sorry

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end
