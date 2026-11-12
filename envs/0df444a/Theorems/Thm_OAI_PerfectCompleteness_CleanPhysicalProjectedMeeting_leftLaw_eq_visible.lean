-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_CleanPhysicalProjectedMeeting_leftLaw_eq_visible
-- name    : OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.leftLaw_eq_visible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:52:24.733887+00:00
-- url     : https://prove2.me/theorems/a1b34c92-c098-4c4e-9474-214e9d5c73c6
-- title:
--   OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.leftLaw_eq_visible: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.leftLaw_eq_visible` of [lean/OAI/Computability/PerfectCompleteness/Repetition/CleanPhysicalProjectedMeeting.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Repetition/CleanPhysicalProjectedMeeting.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting`, with `open scoped Classical`, `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open UniqueGamesTheorem.Foundations.Games`):
--
--   ```lean
--   theorem leftLaw_eq_visible (x : CleanDecoderRate.Sample S) :
--       CleanPhysicalDecoderLaw.leftLaw S F κ σ r ρ A x =
--         HierarchicalProjectedMeeting.leftLaw
--           (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
--           (CleanPhysicalDecoderLaw.physicalProjection S x) upper (h + 1)
--           (HierarchicalProjectedRawPrediction.visibleBackground
--             (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
--             (CleanPhysicalDecoderLaw.physicalProjection S x) rows upper (lower S) A repeats S.cut
--             (visible S (LinearMap.ker A) x))
--           (F.original (CleanNativeReplay.leftSlots S x))
--           (F.arrays (CleanNativeReplay.leftSlots S x))
--           (F.lowerEvent (CleanNativeReplay.leftSlots S x)) κ σ ρ A
--           (HierarchicalProjectedRawPrediction.known (CleanNativeReplay.rightSlots S x)
--             rows upper (lower S) A repeats S.cut (visible S (LinearMap.ker A) x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution` and `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.F2`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.F2`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes`, `OAI.PerfectCompleteness.KeyStrategy.Strategy` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Block`, `OAI.PerfectCompleteness.HierarchicalFrozenTables.LowerNodes`, `OAI.PerfectCompleteness.NodeEmbedding.NumberedDomain`, `OAI.PerfectCompleteness.NodeEmbedding.RowSpace` and `OAI.PerfectCompleteness.TreeCanonical.locationCount` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.ManyGoodRows.RowMap` (definitions bundle `OAIQ252P004` of this split); `OAI.PerfectCompleteness.CleanDecoderRate.Sample`, `OAI.PerfectCompleteness.CleanDecoderRate.Setup`, `OAI.PerfectCompleteness.CleanNativeReplay.leftSlots`, `OAI.PerfectCompleteness.CleanNativeReplay.rightSlots`, `OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.leftLaw`, `OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.nativeLeftFintype`, `OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.physicalProjection`, `OAI.PerfectCompleteness.OriginalDecoderMark.Family` and `OAI.PerfectCompleteness.OriginalDecoderMark.SlotFamily` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.lower`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.visible`, `OAI.PerfectCompleteness.HierarchicalProjectedMeeting.leftLaw`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.known` and `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.visibleBackground` (definitions bundle `OAIQ252P012` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.native_expectation_eq_cleanMeeting` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Repetition/CleanPhysicalProjectedMeeting.lean (declaration OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.leftLaw_eq_visible)

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
import Definitions.Def_OAIQ252P012

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalProjectedMeeting

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] CleanPhysicalDecoderLaw.nativeLeftFintype RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

variable {Sample : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch rows n t Sample) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (a : Block rows (lower S)) (threshold : ℝ)

theorem leftLaw_eq_visible (x : CleanDecoderRate.Sample S) :
    CleanPhysicalDecoderLaw.leftLaw S F κ σ r ρ A x =
      HierarchicalProjectedMeeting.leftLaw
        (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
        (CleanPhysicalDecoderLaw.physicalProjection S x) upper (h + 1)
        (HierarchicalProjectedRawPrediction.visibleBackground
          (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
          (CleanPhysicalDecoderLaw.physicalProjection S x) rows upper (lower S) A repeats S.cut
          (visible S (LinearMap.ker A) x))
        (F.original (CleanNativeReplay.leftSlots S x))
        (F.arrays (CleanNativeReplay.leftSlots S x))
        (F.lowerEvent (CleanNativeReplay.leftSlots S x)) κ σ ρ A
        (HierarchicalProjectedRawPrediction.known (CleanNativeReplay.rightSlots S x)
          rows upper (lower S) A repeats S.cut (visible S (LinearMap.ker A) x)) := by
  sorry

end
end PerfectCompleteness.CleanPhysicalProjectedMeeting

end

end OAI
end
