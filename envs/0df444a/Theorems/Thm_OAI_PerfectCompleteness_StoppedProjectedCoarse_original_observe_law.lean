-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_StoppedProjectedCoarse_original_observe_law
-- name    : OAI.PerfectCompleteness.StoppedProjectedCoarse.original_observe_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:05:02.390328+00:00
-- url     : https://prove2.me/theorems/2578a6f1-266b-4d03-930c-bab27af37a4b
-- title:
--   OAI.PerfectCompleteness.StoppedProjectedCoarse.original_observe_law: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.StoppedProjectedCoarse.original_observe_law` of [lean/OAI/Computability/PerfectCompleteness/Foundations/StoppedProjectedCoarseLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/StoppedProjectedCoarseLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.StoppedProjectedCoarse`, with `open scoped Classical`, `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open UniqueGamesTheorem.Foundations.Games`, `open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)`):
--
--   ```lean
--   theorem original_observe_law (outer : FiniteDistribution O) (r : Nat) :
--       HeterogeneousPairAdvice.observedLaw S
--           (pairLaw clauses rows repeats hupper hij designated hbranch hrows flag σ outer) r =
--         (HierarchicalAdviceFamily.originalLaw S outer r).pushforward
--           (HierarchicalAdviceFamily.observe S r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2` and `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.GeometricCutSplit.Prefix`, `OAI.PerfectCompleteness.KeyStrategy.Strategy` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Block`, `OAI.PerfectCompleteness.PreliminarySampler.Questions`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsDecidableEq`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsFintype`, `OAI.PerfectCompleteness.SourceClause.NormalizedClause`, `OAI.PerfectCompleteness.TreeCanonical.locationCount` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.GeometricCutSplit.prefixDepthFintype` (definitions bundle `OAIQ252P005` of this split); `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Advice`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.OriginalSample`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.originalLaw` and `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Experiment` (definitions bundle `OAIQ252P011` of this split); `OAI.PerfectCompleteness.HeterogeneousPairAdvice.coarseFintype`, `OAI.PerfectCompleteness.HeterogeneousPairAdvice.observedLaw`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Coarse`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Observation` and `OAI.PerfectCompleteness.HierarchicalAdviceFamily.observe` (definitions bundle `OAIQ252P015` of this split); `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.Sample`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.Inner`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.Outer`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.cut`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.experiment`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.lower`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.projectedSlots` and `OAI.PerfectCompleteness.StoppedProjectedExperiment.upper` (definitions bundle `OAIQ252P017` of this split); `OAI.PerfectCompleteness.StoppedProjectedCoarse.adviceFintype`, `OAI.PerfectCompleteness.StoppedProjectedCoarse.coarseFintype`, `OAI.PerfectCompleteness.StoppedProjectedCoarse.pairLaw` and `OAI.PerfectCompleteness.StoppedProjectedCoarse.projectedSampleFintype` (definitions bundle `OAIQ252P018` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedStoppedActualBounds.coarseVariation_le_pairedVariation` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/StoppedProjectedCoarseLemmas.lean (declaration OAI.PerfectCompleteness.StoppedProjectedCoarse.original_observe_law)

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
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
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
import Mathlib.Algebra.Polynomial.Inductions
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
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
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
import Definitions.Def_OAIQ252P018

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedCoarse

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

local notation "O" => StoppedProjectedExperiment.Outer
  (branch := branch) (n := n) (j := j) (t := t) (m := m)

local notation "S" => StoppedProjectedExperiment.experiment clauses rows repeats hupper hij
  designated hbranch hrows flag σ

local instance fixedBackgroundFintype_r9aee4c_1
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
  HierarchicalUsefulCollision.backgroundFintype (rows := rows) slots upper
attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedCoarse.backgroundFintype
local instance rowSpaceFintype_r9aee4c_1 (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) :=
  HierarchicalPairCoarse.rowSpaceFintype (S o)
attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedCoarse.coarseFintype
local instance inputFintype_r9aee4c_1 (o : O) (background : HierarchicalAdviceExperiment.Background (S o)) :
    Fintype (HierarchicalAdviceExperiment.Input (S o) background) :=
  HierarchicalAdviceExperiment.inputFintype (S o) background
attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedCoarse.projectedSampleFintype
attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedCoarse.adviceFintype
attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedCoarse.originalFiberFintype
theorem original_observe_law (outer : FiniteDistribution O) (r : Nat) :
    HeterogeneousPairAdvice.observedLaw S
        (pairLaw clauses rows repeats hupper hij designated hbranch hrows flag σ outer) r =
      (HierarchicalAdviceFamily.originalLaw S outer r).pushforward
        (HierarchicalAdviceFamily.observe S r) := by
  sorry

end
end PerfectCompleteness.StoppedProjectedCoarse

end

end OAI
end
