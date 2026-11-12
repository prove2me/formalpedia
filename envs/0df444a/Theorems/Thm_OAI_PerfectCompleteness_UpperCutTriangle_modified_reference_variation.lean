-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_UpperCutTriangle_modified_reference_variation
-- name    : OAI.PerfectCompleteness.UpperCutTriangle.modified_reference_variation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:20:30.857012+00:00
-- url     : https://prove2.me/theorems/c5820763-0984-4a8c-bed4-f4808f85debd
-- title:
--   OAI.PerfectCompleteness.UpperCutTriangle.modified_reference_variation: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.UpperCutTriangle.modified_reference_variation` of [lean/OAI/Computability/PerfectCompleteness/Decoding/UpperCutTriangle.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/UpperCutTriangle.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.UpperCutTriangle`, with `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open OriginalWholeCutTape WholeArrayInteriorExterior`, `open UniqueGamesTheorem.Foundations.Games`, `open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)`, `open scoped Classical`):
--
--   ```lean
--   theorem modified_reference_variation (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
--       (hcut : i + 1 ≤ j + 1) (slots : Slots branch n → Fin t → MixedSupport.Slot)
--       (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : 0 < rows (j + 1))
--       (projected : (pref : Prefix branch j i) → (c : Fin (branch i)) → Z pref c →
--         Slots branch i → Fin t → MixedSupport.Slot)
--       (projection : ∀ pref c z s a, MixedSupport.Projection
--         (childSlots (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots) c s a)
--         (projected pref c z s a))
--       (choiceLaw : (pref : Prefix branch j i) → (c : Fin (branch i)) → FiniteDistribution (Z pref c))
--       (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
--       (modifiedPairLaw rows repeats p hcut slots hbranch hrows projected projection choiceLaw β hβ hβ').totalVariation
--         (HierarchicalAgreementMean.referenceLaw slots (upperNode p)
--           (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
--           (by simpa only [upperNode_height] using hrows)) ≤
--         Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch i t
--           (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows : ℝ) - 1)) ^ branch i - 1) / 2 +
--         Real.sqrt ((ChildBlockCardinality.bound branch i t
--           (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows : ℝ) ^ 2 / branch i) / 2 +
--         Real.sqrt ((ChildBlockCardinality.bound branch j t
--           (OriginalCutCalls.count rows repeats n (j + 1) + 1) rows : ℝ) ^ 2 / branch j) / 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.DescendantSpaces.Path`, `OAI.PerfectCompleteness.GeometricCutSplit.Prefix`, `OAI.PerfectCompleteness.MixedSupport.Projection`, `OAI.PerfectCompleteness.MixedSupport.Slot`, `OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` and `OAI.PerfectCompleteness.MixedSupport.Slot.Domain` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.OriginalCutCalls.count` and `OAI.PerfectCompleteness.UpperScalarCutCalls.count` (definitions bundle `OAIQ252P002` of this split); `OAI.PerfectCompleteness.HierarchicalAgreementMean.Background`, `OAI.PerfectCompleteness.HierarchicalArrays.Block`, `OAI.PerfectCompleteness.NodeEmbedding.NumberedDomain`, `OAI.PerfectCompleteness.NodeEmbedding.RowSpace`, `OAI.PerfectCompleteness.TreeCanonical.locationCount`, `OAI.PerfectCompleteness.TreeCanonical.numberedSlots`, `OAI.PerfectCompleteness.TreeSourceSpaces.childSlots` and `OAI.PerfectCompleteness.DescendantSpaces.Path.append` (definitions bundle `OAIQ252P003` of this split); `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.totalVariation` (definitions bundle `OAIQ252P006` of this split); `OAI.PerfectCompleteness.ChildBlockCardinality.bound`, `OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode` and `OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.GeometricCutSplit.prefixPath`, `OAI.PerfectCompleteness.HierarchicalAgreementMean.Matrix`, `OAI.PerfectCompleteness.HierarchicalAgreementMean.PairRecord`, `OAI.PerfectCompleteness.HierarchicalAgreementMean.referenceLaw` and `OAI.PerfectCompleteness.UpperCutTriangle.Prefix` (definitions bundle `OAIQ252P011` of this split); `OAI.PerfectCompleteness.OriginalWholeCutTape.cutSlots` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.OriginalOwnBucketSplit.backgroundLaw`, `OAI.PerfectCompleteness.UpperCutTriangle.backgroundFintype` and `OAI.PerfectCompleteness.UpperCutTriangle.modifiedPairLaw` (definitions bundle `OAIQ252P018` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedUpperCutTriangle.original_reference_lt` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/UpperCutTriangle.lean (declaration OAI.PerfectCompleteness.UpperCutTriangle.modified_reference_variation)

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

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperCutTriangle

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n j i t : Nat}

variable {Z : Prefix branch j i → Fin (branch i) → Type*}
  [∀ pref c, Fintype (Z pref c)]

attribute [local instance] OAI.PerfectCompleteness.UpperCutTriangle.backgroundFintype
local instance rowSpaceFintype_rca4bb7_1 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
theorem modified_reference_variation (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (hcut : i + 1 ≤ j + 1) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : 0 < rows (j + 1))
    (projected : (pref : Prefix branch j i) → (c : Fin (branch i)) → Z pref c →
      Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ pref c z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots) c s a)
      (projected pref c z s a))
    (choiceLaw : (pref : Prefix branch j i) → (c : Fin (branch i)) → FiniteDistribution (Z pref c))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (modifiedPairLaw rows repeats p hcut slots hbranch hrows projected projection choiceLaw β hβ hβ').totalVariation
      (HierarchicalAgreementMean.referenceLaw slots (upperNode p)
        (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
        (by simpa only [upperNode_height] using hrows)) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows : ℝ) - 1)) ^ branch i - 1) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows : ℝ) ^ 2 / branch i) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch j t
        (OriginalCutCalls.count rows repeats n (j + 1) + 1) rows : ℝ) ^ 2 / branch j) / 2 := by
  sorry

end
end PerfectCompleteness.UpperCutTriangle

end

end OAI
end
