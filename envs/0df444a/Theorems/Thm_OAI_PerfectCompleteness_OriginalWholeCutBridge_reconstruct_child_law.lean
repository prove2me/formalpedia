-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_OriginalWholeCutBridge_reconstruct_child_law
-- name    : OAI.PerfectCompleteness.OriginalWholeCutBridge.reconstruct_child_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:19:20.013732+00:00
-- url     : https://prove2.me/theorems/1a3a2f54-6c02-44a1-a17e-b583e48239d8
-- title:
--   OAI.PerfectCompleteness.OriginalWholeCutBridge.reconstruct_child_law: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.OriginalWholeCutBridge.reconstruct_child_law` of [lean/OAI/Computability/PerfectCompleteness/Foundations/OriginalWholeCutBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/OriginalWholeCutBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.OriginalWholeCutBridge`, with `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw`, `open UniqueGamesTheorem.Foundations.Games`, `open scoped Classical`):
--
--   ```lean
--   theorem reconstruct_child_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
--       (chosen : Fin (branch m)) (q : Path branch m k)
--       (slots : Slots branch n → Fin t → MixedSupport.Slot) :
--       ((exteriorLaw rows repeats p slots).product
--           ((OriginalChildBlocks.sourceLaw (OriginalCutCalls.count rows repeats n (m + 1))
--             rows repeats chosen q (cutSlots p slots)).pushforward
--               (OriginalChildBlocks.observed (OriginalCutCalls.count rows repeats n (m + 1))
--                 rows repeats chosen q (cutSlots p slots)))).pushforward
--                   (reconstruct rows repeats p slots) =
--         WholeArraySampler.law rows repeats (p.append (.step chosen q)) slots
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.DescendantSpaces.Path`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes`, `OAI.PerfectCompleteness.HierarchicalArrays.nodesDecidableEq`, `OAI.PerfectCompleteness.HierarchicalArrays.nodesFintype`, `OAI.PerfectCompleteness.MixedSupport.Slot`, `OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` and `OAI.PerfectCompleteness.MixedSupport.Slot.Domain` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.OriginalCutCalls.count` (definitions bundle `OAIQ252P002` of this split); `OAI.PerfectCompleteness.CutChildGrouping.Assembled`, `OAI.PerfectCompleteness.HierarchicalArrays.Arrays`, `OAI.PerfectCompleteness.HierarchicalArrays.nodeSlots`, `OAI.PerfectCompleteness.OriginalChildScalars.ScalarTape`, `OAI.PerfectCompleteness.RecursiveSampler.DrawIndex`, `OAI.PerfectCompleteness.RecursiveSampler.DrawSpace`, `OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq`, `OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype`, `OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype`, `OAI.PerfectCompleteness.TreeSourceSpaces.Domain`, `OAI.PerfectCompleteness.TreeSourceSpaces.H`, `OAI.PerfectCompleteness.TreeSourceSpaces.LeafDomain`, `OAI.PerfectCompleteness.WholeArraySampler.Tape`, `OAI.PerfectCompleteness.WholeArraySampler.law`, `OAI.PerfectCompleteness.WholeArraySampler.spaceFintype`, `OAI.PerfectCompleteness.WholeArraySampler.tapeFintype`, `OAI.PerfectCompleteness.DescendantSpaces.Path.append`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.product` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.CutChildGrouping.assembledFintype` and `OAI.PerfectCompleteness.OriginalChildBlocks.SourceTape` (definitions bundle `OAIQ252P008` of this split); `OAI.PerfectCompleteness.OriginalWholeCutTape.Exterior` and `OAI.PerfectCompleteness.OriginalWholeCutTape.cutSlots` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.OriginalChildBlocks.observed` and `OAI.PerfectCompleteness.OriginalChildBlocks.sourceLaw` (definitions bundle `OAIQ252P013` of this split); `OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype` and `OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorLaw` (definitions bundle `OAIQ252P017` of this split); `OAI.PerfectCompleteness.OriginalWholeCutBridge.reconstruct` (definitions bundle `OAIQ252P018` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.OriginalWholeCutComparison.totalVariation_le` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/OriginalWholeCutBridge.lean (declaration OAI.PerfectCompleteness.OriginalWholeCutBridge.reconstruct_child_law)

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
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Definitions.Def_OAIQ252P018

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutBridge

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

theorem reconstruct_child_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
        ((OriginalChildBlocks.sourceLaw (OriginalCutCalls.count rows repeats n (m + 1))
          rows repeats chosen q (cutSlots p slots)).pushforward
            (OriginalChildBlocks.observed (OriginalCutCalls.count rows repeats n (m + 1))
              rows repeats chosen q (cutSlots p slots)))).pushforward
                (reconstruct rows repeats p slots) =
      WholeArraySampler.law rows repeats (p.append (.step chosen q)) slots := by
  sorry

end
end PerfectCompleteness.OriginalWholeCutBridge

end

end OAI
end
