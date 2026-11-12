-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_LowerProjectedFiberAverage_rawCollision_eq_mean
-- name    : OAI.PerfectCompleteness.LowerProjectedFiberAverage.rawCollision_eq_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:57:51.958905+00:00
-- url     : https://prove2.me/theorems/4d1f7eae-7ef6-4d7e-922d-907f7da892b0
-- title:
--   OAI.PerfectCompleteness.LowerProjectedFiberAverage.rawCollision_eq_mean: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.LowerProjectedFiberAverage.rawCollision_eq_mean` of [lean/OAI/Computability/PerfectCompleteness/Decoding/LowerProjectedFiberAverage.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/LowerProjectedFiberAverage.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.LowerProjectedFiberAverage`, with `open scoped Classical`, `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open WholeCutGrouping`, `open UniqueGamesTheorem.Foundations.Games`):
--
--   ```lean
--   theorem rawCollision_eq_mean (s : Nat)
--       (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r) :
--       rawCollision path slots projected projection upper level hbranch d a exterior A s table =
--         (backgroundLaw path projected a).expectation (fun bg =>
--           ((FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)).product
--             (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d))).probability
--               (ProjectedFiberSquare.restrictedPair slots projected projection upper level hbranch d A
--                 (ProjectedFiberRawPair.direction path upper level d hnode a)
--                 (baseline path projected a exterior bg) s table))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.expectation` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.BucketSampler.Direction`, `OAI.PerfectCompleteness.DescendantSpaces.Path`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes`, `OAI.PerfectCompleteness.MixedSupport.Projection`, `OAI.PerfectCompleteness.MixedSupport.Slot` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Block`, `OAI.PerfectCompleteness.HierarchicalArrays.nodeSlots`, `OAI.PerfectCompleteness.HierarchicalFrozenTables.LowerNodes`, `OAI.PerfectCompleteness.HierarchicalLeftDecoder.LowerNode`, `OAI.PerfectCompleteness.TreeSourceSpaces.Domain`, `OAI.PerfectCompleteness.WholeArraySampler.spaceFintype`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.product` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.uniform` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.ManyGoodRows.RowMap` (definitions bundle `OAIQ252P004` of this split); `OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode`, `OAI.PerfectCompleteness.WholeCutGrouping.Exterior` and `OAI.PerfectCompleteness.WholeCutGrouping.cutSlots` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.LowerDirectionFiber.Other` and `OAI.PerfectCompleteness.LowerDirectionFiber.pivot` (definitions bundle `OAIQ252P008` of this split); `OAI.PerfectCompleteness.LowerCutFiberDisintegration.Quotient`, `OAI.PerfectCompleteness.LowerCutFiberDisintegration.Scalar`, `OAI.PerfectCompleteness.LowerCutPairBackground.Complement`, `OAI.PerfectCompleteness.ProjectedFiberRawPair.direction`, `OAI.PerfectCompleteness.ProjectedLowerFiber.Scalar` and `OAI.PerfectCompleteness.ProjectedLowerFiber.lower` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype` (definitions bundle `OAIQ252P015` of this split); `OAI.PerfectCompleteness.LowerProjectedFiberAverage.Background`, `OAI.PerfectCompleteness.LowerProjectedFiberAverage.backgroundLaw`, `OAI.PerfectCompleteness.LowerProjectedFiberAverage.baseline`, `OAI.PerfectCompleteness.LowerProjectedFiberAverage.rawCollision`, `OAI.PerfectCompleteness.ProjectedFiberSquare.restrictedPair` and `OAI.PerfectCompleteness.ProjectedLowerFiber.UpperTable` (definitions bundle `OAIQ252P017` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.LowerProjectedFiberAverage.meanSuccess_square_le` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/LowerProjectedFiberAverage.lean (declaration OAI.PerfectCompleteness.LowerProjectedFiberAverage.rawCollision_eq_mean)

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
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Definitions.Def_OAIQ252P017

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerProjectedFiberAverage

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n m t : Nat}
  (path : Path branch n (m + 1))
  (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : Exterior rows repeats path projected)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)

local instance rowSpaceFintype_r128264_1 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r128264_1 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
theorem rawCollision_eq_mean (s : Nat)
    (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r) :
    rawCollision path slots projected projection upper level hbranch d a exterior A s table =
      (backgroundLaw path projected a).expectation (fun bg =>
        ((FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)).product
          (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d))).probability
            (ProjectedFiberSquare.restrictedPair slots projected projection upper level hbranch d A
              (ProjectedFiberRawPair.direction path upper level d hnode a)
              (baseline path projected a exterior bg) s table)) := by
  sorry

end
end PerfectCompleteness.LowerProjectedFiberAverage

end

end OAI
end
