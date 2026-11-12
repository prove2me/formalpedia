-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_WholeCutGroupedProjection_evaluateGrouped_pullback
-- name    : OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:52:02.682746+00:00
-- url     : https://prove2.me/theorems/feb5c9cc-6ae1-42cf-80ff-2736edea39a2
-- title:
--   OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback` of [lean/OAI/Computability/PerfectCompleteness/Decoding/WholeCutGroupedProjection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/WholeCutGroupedProjection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.WholeCutGroupedProjection`, with `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open UniqueGamesTheorem.Foundations.Games`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem evaluateGrouped_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
--       ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
--         (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
--         (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
--         (_ : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
--           HEq (q s k) (MixedSupport.Projection.keep (left s k)))
--         (ext : WholeCutGrouping.Exterior rows repeats p right)
--         (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
--           (WholeCutGrouping.cutSlots p right) rows),
--       evaluateGrouped rows repeats p left
--           (WholeCutExteriorTransport.equiv rows repeats p right left (fun s h => (hs s h).symm) ext)
--           (ChildAssemblyProjection.rawPullback rows (CutGroupedProjection.cutProjection p q) children) =
--         ChildBlockProjection.arraysPullback rows q
--           (evaluateGrouped rows repeats p right ext children)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.PointwiseSpaces.squareSpace`, `OAI.PerfectCompleteness.RecursiveSpaces.Slots` and `OAI.PerfectCompleteness.TreeSourceSpaces.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.DescendantSpaces.Path`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes`, `OAI.PerfectCompleteness.MixedSupport.Projection`, `OAI.PerfectCompleteness.MixedSupport.Slot` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback`, `OAI.PerfectCompleteness.CutChildGrouping.Child`, `OAI.PerfectCompleteness.CutChildGrouping.Raw`, `OAI.PerfectCompleteness.HierarchicalArrays.Arrays`, `OAI.PerfectCompleteness.HierarchicalArrays.nodeSlots`, `OAI.PerfectCompleteness.TreeSourceSpaces.Domain`, `OAI.PerfectCompleteness.TreeSourceSpaces.H` and `OAI.PerfectCompleteness.TreeSourceSpaces.childSlots` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.ChildAssemblyProjection.rawPullback`, `OAI.PerfectCompleteness.WholeCutCalls.Index`, `OAI.PerfectCompleteness.WholeCutExteriorTransport.Outside`, `OAI.PerfectCompleteness.WholeCutExteriorTransport.equiv`, `OAI.PerfectCompleteness.WholeCutGrouping.Exterior` and `OAI.PerfectCompleteness.WholeCutGrouping.cutSlots` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.CutGroupedProjection.cutProjection` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped` (definitions bundle `OAIQ252P015` of this split).
--
--   **Used by.** The proofs of `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.leftLaw_eq_visible` and `OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical` of this split import it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/WholeCutGroupedProjection.lean (declaration OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback)

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
import Definitions.Def_OAIQ252P012
import Definitions.Def_OAIQ252P015

section

attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutGroupedProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluateGrouped_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
      (_ : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k)))
      (ext : WholeCutGrouping.Exterior rows repeats p right)
      (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p right) rows),
    evaluateGrouped rows repeats p left
        (WholeCutExteriorTransport.equiv rows repeats p right left (fun s h => (hs s h).symm) ext)
        (ChildAssemblyProjection.rawPullback rows (CutGroupedProjection.cutProjection p q) children) =
      ChildBlockProjection.arraysPullback rows q
        (evaluateGrouped rows repeats p right ext children) := by
  sorry

end
end PerfectCompleteness.WholeCutGroupedProjection

end

end OAI
end
