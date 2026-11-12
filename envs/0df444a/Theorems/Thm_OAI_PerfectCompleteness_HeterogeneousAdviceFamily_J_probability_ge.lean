-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_HeterogeneousAdviceFamily_J_probability_ge
-- name    : OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:44:44.54186+00:00
-- url     : https://prove2.me/theorems/e4aa3337-531c-4474-ac1c-4c84c2c497c2
-- title:
--   OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge` of [lean/OAI/Computability/PerfectCompleteness/Foundations/HeterogeneousAdviceFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/HeterogeneousAdviceFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.HeterogeneousAdviceFamily`, with `open scoped BigOperators Classical`, `open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)`, `open UniqueGamesTheorem.Fourier.MatrixLevelBridge`, `open UniqueGamesTheorem.Appendix.RankLevelFilter`, `open UniqueGamesTheorem.Foundations.Games`, `open PerfectCompleteness.ManyGoodRows`):
--
--   ```lean
--   theorem J_probability_ge (μ : FiniteDistribution P)
--       (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r ℓ : Nat)
--       (hdim : ∀ p, Module.finrank F2 (F p) ≤ ℓ)
--       (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
--       (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
--       (hmean : 2 * η ≤ μ.expectation (fun p => PartialTableInverse.nonzeroAgreement (f p))) :
--       (η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2 ≤
--         (law (E := E) (F := F) μ r).probability (J f r ρ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2`, `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.expectation` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.node` and `OAI.UniqueGamesTheorem.Fourier.MatrixLevelBridge.levelCutoffConstant` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.ManyGoodRows.RowMap` (definitions bundle `OAIQ252P004` of this split); `OAI.PerfectCompleteness.PartialTableInverse.nonzeroAgreement` (definitions bundle `OAIQ252P006` of this split); `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J`, `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.Sample` and `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.law` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction_difference` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/HeterogeneousAdviceFamily.lean (declaration OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
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
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P011

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HeterogeneousAdviceFamily

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P] {E F Y : P → Type*}
  [∀ p, AddCommGroup (E p)] [∀ p, Module F2 (E p)]
  [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module F2 (F p)]
  [∀ p, FiniteDimensional F2 (F p)] [∀ p, Fintype (F p)]
  [∀ p, Fintype (Y p)]

variable [∀ p, Nontrivial (F p)]

theorem J_probability_ge (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r ℓ : Nat)
    (hdim : ∀ p, Module.finrank F2 (F p) ≤ ℓ)
    (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ μ.expectation (fun p => PartialTableInverse.nonzeroAgreement (f p))) :
    (η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2 ≤
      (law (E := E) (F := F) μ r).probability (J f r ρ) := by
  sorry

end
end PerfectCompleteness.HeterogeneousAdviceFamily

end

end OAI
end
