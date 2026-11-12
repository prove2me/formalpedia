-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_OddListGame_repetition_halfRate
-- name    : OAI.PerfectCompleteness.OddListGame.repetition_halfRate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:46:00.108863+00:00
-- url     : https://prove2.me/theorems/dc2d49bf-bba7-4431-abf2-fba9ed1015f0
-- title:
--   OAI.PerfectCompleteness.OddListGame.repetition_halfRate: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.OddListGame.repetition_halfRate` of [lean/OAI/Computability/PerfectCompleteness/Reduction/OddListGame.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Reduction/OddListGame.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.OddListGame`, with `open scoped BigOperators`, `open UniqueGamesTheorem.Foundations.Games`, `open OddLists FiniteListSampling`):
--
--   ```lean
--   theorem repetition_halfRate {s L : Nat} [NeZero s] [Nonempty A₁] [Nonempty A₂]
--       (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
--       (projection : E → A₁ → A₂)
--       (determined : (base μ left right projection).EndpointDetermined)
--       (gap : (s : ℝ) ^ 2 * (base μ left right projection).value ≤ 1 / 2)
--       (hL : 0 < L)
--       (alphabet : UniqueGamesTheorem.Foundations.Repetition.logTwo
--         ((Fintype.card (OddList s A₁) : ℝ) * (Fintype.card (OddList s A₂) : ℝ)) ≤ L)
--       (n : Nat) :
--       ((game s μ left right projection).repetition n).value ≤
--         (RepetitionRate.halfRate L : ℝ) ^ n
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.OddLists.OddList` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.RepetitionRate.halfRate` and `OAI.UniqueGamesTheorem.Foundations.Repetition.logTwo` (definitions bundle `OAIQ252P002` of this split); `OAI.PerfectCompleteness.OccurrenceGame.value` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat` (definitions bundle `OAIQ252P006` of this split); `OAI.PerfectCompleteness.OccurrenceGame.EndpointDetermined`, `OAI.PerfectCompleteness.OccurrenceGame.repetition`, `OAI.PerfectCompleteness.OddListGame.base` and `OAI.PerfectCompleteness.OddListGame.game` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.SourceOddLists.repetition_halfRate` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Reduction/OddListGame.lean (declaration OAI.PerfectCompleteness.OddListGame.repetition_halfRate)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
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
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std
import Definitions.Def_OAIQ252P011

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OddListGame

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open OddLists FiniteListSampling

noncomputable section

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq A₁] [DecidableEq A₂]

theorem repetition_halfRate {s L : Nat} [NeZero s] [Nonempty A₁] [Nonempty A₂]
    (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂)
    (determined : (base μ left right projection).EndpointDetermined)
    (gap : (s : ℝ) ^ 2 * (base μ left right projection).value ≤ 1 / 2)
    (hL : 0 < L)
    (alphabet : UniqueGamesTheorem.Foundations.Repetition.logTwo
      ((Fintype.card (OddList s A₁) : ℝ) * (Fintype.card (OddList s A₂) : ℝ)) ≤ L)
    (n : Nat) :
    ((game s μ left right projection).repetition n).value ≤
      (RepetitionRate.halfRate L : ℝ) ^ n := by
  sorry

end
end PerfectCompleteness.OddListGame

end

end OAI
end
