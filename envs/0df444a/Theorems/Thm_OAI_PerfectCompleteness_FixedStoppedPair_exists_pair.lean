-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedPair_exists_pair
-- name    : OAI.PerfectCompleteness.FixedStoppedPair.exists_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:03:57.66353+00:00
-- url     : https://prove2.me/theorems/c3f11136-4abd-4ce7-be7b-cd497519f18f
-- title:
--   OAI.PerfectCompleteness.FixedStoppedPair.exists_pair: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.FixedStoppedPair.exists_pair` of [lean/OAI/Computability/PerfectCompleteness/Reduction/FixedStoppedPair.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Reduction/FixedStoppedPair.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.FixedStoppedPair`, with `open FixedParameters FixedRows`):
--
--   ```lean
--   theorem exists_pair (input : List Bool) (strategy : FixedPreliminaryGame.Strategy p input)
--       (hsuccess : InitialParameters.epsilon δ ≤
--         (FixedPreliminaryGame.game p input).success strategy) :
--       ∃ i j : Fin p.plan.depth, i < j ∧
--         InitialParameters.simultaneous δ + 2 * p.accuracy ≤
--           (StoppedSharedSampler.stoppedLaw
--             (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
--             (rows p.plan) (repeats p.plan) (cut := i.val)
--             (Nat.succ_le_of_lt i.isLt) (fun k _ => branch_pos p k)
--             (fun k => FixedPreliminaryGame.rows_pos p (k + 1))).probability
--               (StoppedSharedEvents.pair
--                 (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy
--                 (Nat.succ_le_of_lt i.isLt) (fun k _ => branch_pos p k) i j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.BinaryLanguage.totalRename`, `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Foundations.Target.Clause`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` and `OAI.UniqueGamesTheorem.Foundations.Target.Formula` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.BucketSampler.Direction`, `OAI.PerfectCompleteness.BucketSampler.F2`, `OAI.PerfectCompleteness.GeometricCutSplit.Prefix`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes`, `OAI.PerfectCompleteness.HierarchicalArrays.nodesDecidableEq`, `OAI.PerfectCompleteness.HierarchicalArrays.nodesFintype`, `OAI.PerfectCompleteness.InitialParameters.epsilon`, `OAI.PerfectCompleteness.InitialParameters.simultaneous` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.CanonicalDirections.Tuple`, `OAI.PerfectCompleteness.GeometricPath.leafPath`, `OAI.PerfectCompleteness.GeometricPath.nodeAtLevel`, `OAI.PerfectCompleteness.HierarchicalArrays.Arrays`, `OAI.PerfectCompleteness.HierarchicalArrays.nodeSlots`, `OAI.PerfectCompleteness.HierarchicalArrays.sourceSlots`, `OAI.PerfectCompleteness.PrefixTests.LevelDirection`, `OAI.PerfectCompleteness.PreliminarySampler.Base`, `OAI.PerfectCompleteness.PreliminarySampler.Choice`, `OAI.PerfectCompleteness.PreliminarySampler.Questions`, `OAI.PerfectCompleteness.PreliminarySampler.endpoints`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsDecidableEq`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsFintype`, `OAI.PerfectCompleteness.TreeSourceSpaces.Domain`, `OAI.PerfectCompleteness.TreeSourceSpaces.H`, `OAI.PerfectCompleteness.WholeArraySampler.spaceFintype`, `OAI.PerfectCompleteness.WholeArraySampler.tapeFintype` and `OAI.PerfectCompleteness.CompletionSoundness.LegalProjectionGame.success` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.GeometricCutSplit.prefixDepthFintype` (definitions bundle `OAIQ252P005` of this split); `OAI.PerfectCompleteness.FixedRows.rows`, `OAI.PerfectCompleteness.HierarchicalGame.LeftLabel`, `OAI.PerfectCompleteness.HierarchicalGame.LeftVertex`, `OAI.PerfectCompleteness.HierarchicalGame.RightLabel`, `OAI.PerfectCompleteness.HierarchicalGame.RightVertex`, `OAI.PerfectCompleteness.PreliminarySampler.ArrayTape`, `OAI.PerfectCompleteness.PreliminarySampler.Raw`, `OAI.PerfectCompleteness.PreliminarySampler.family` and `OAI.PerfectCompleteness.FixedRows.Plan` (definitions bundle `OAIQ252P008` of this split); `OAI.PerfectCompleteness.StoppedSharedSampler.Context` (definitions bundle `OAIQ252P011` of this split); `OAI.PerfectCompleteness.FixedRows.repeats` and `OAI.PerfectCompleteness.PCPSource.normalizedFormula` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.FixedRows.sourceLength` (definitions bundle `OAIQ252P013` of this split); `OAI.PerfectCompleteness.FixedParameters.Parameters`, `OAI.PerfectCompleteness.FixedParameters.branch`, `OAI.PerfectCompleteness.FixedParameters.branch_pos`, `OAI.PerfectCompleteness.FixedPreliminaryGame.rows_pos`, `OAI.PerfectCompleteness.PCPSource.clauseCount_neZero` and `OAI.PerfectCompleteness.PCPSource.clauseFamily` (definitions bundle `OAIQ252P016` of this split); `OAI.PerfectCompleteness.StoppedSharedEvents.pair`, `OAI.PerfectCompleteness.StoppedSharedSampler.Record` and `OAI.PerfectCompleteness.StoppedSharedSampler.stoppedLaw` (definitions bundle `OAIQ252P017` of this split); `OAI.PerfectCompleteness.FixedPreliminaryGame.Strategy` and `OAI.PerfectCompleteness.FixedPreliminaryGame.game` (definitions bundle `OAIQ252P018` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Reduction/FixedStoppedPair.lean (declaration OAI.PerfectCompleteness.FixedStoppedPair.exists_pair)

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

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedPair

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem exists_pair (input : List Bool) (strategy : FixedPreliminaryGame.Strategy p input)
    (hsuccess : InitialParameters.epsilon δ ≤
      (FixedPreliminaryGame.game p input).success strategy) :
    ∃ i j : Fin p.plan.depth, i < j ∧
      InitialParameters.simultaneous δ + 2 * p.accuracy ≤
        (StoppedSharedSampler.stoppedLaw
          (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
          (rows p.plan) (repeats p.plan) (cut := i.val)
          (Nat.succ_le_of_lt i.isLt) (fun k _ => branch_pos p k)
          (fun k => FixedPreliminaryGame.rows_pos p (k + 1))).probability
            (StoppedSharedEvents.pair
              (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy
              (Nat.succ_le_of_lt i.isLt) (fun k _ => branch_pos p k) i j) := by
  sorry

end
end PerfectCompleteness.FixedStoppedPair

end

end OAI
end
