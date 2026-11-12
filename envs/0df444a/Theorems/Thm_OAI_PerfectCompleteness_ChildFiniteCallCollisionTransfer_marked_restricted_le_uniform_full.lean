-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_ChildFiniteCallCollisionTransfer_marked_restricted_le_uniform_full
-- name    : OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:47:58.342221+00:00
-- url     : https://prove2.me/theorems/15cb803c-7079-4563-90aa-9de3b2b997f8
-- title:
--   OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full` of [lean/OAI/Computability/PerfectCompleteness/Decoding/ChildFiniteCallCollisionTransfer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/ChildFiniteCallCollisionTransfer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer`, with `open scoped Classical`, `open RecursiveSpaces TreeSourceSpaces`, `open UniqueGamesTheorem.Foundations.Games`):
--
--   ```lean
--   theorem marked_restricted_le_uniform_full
--       (rows : Nat → Nat)
--       (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
--       (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
--       (p : ∀ i z s k, MixedSupport.Projection
--         (childSlots slots i s k) (projected i z s k))
--       (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
--       (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
--       (F₀ F₁ : CutChildGrouping.Raw (C := C) slots rows →
--         Option (ChildBilinearCollisionTransfer.ParentForm slots)) :
--       (SparseReplacement.markedLaw
--           (fun i => FiniteDistribution.uniform
--             (ChildCallNumbering.Raw (C := C) rows (childSlots slots i)))
--           (ChildCallNumberingLaws.replacementLaws (C := C) rows (childSlots slots)
--             projected p choiceLaw) β hβ hβ'.le).probability
--         (fun z => BilinearCollisionTransfer.restrictedCollision
--           (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) ≤
--         (FiniteProduct.law (fun i => FiniteDistribution.uniform
--           (ChildCallNumbering.Raw (C := C) rows (childSlots slots i)))).probability
--             (fun x => BilinearCollisionTransfer.fullCollision (F₀ x) (F₁ x)) +
--           2 * (β * (ChildBlockCardinality.bound branch n t (Fintype.card C) rows : ℝ) /
--             (1 - β)) +
--           Real.sqrt ((1 + β ^ 2 *
--             ((ChildBlockCardinality.bound branch n t (Fintype.card C) rows : ℝ) - 1)) ^
--               branch n - 1) / 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.BilinearCollisionTransfer.fullCollision`, `OAI.PerfectCompleteness.BilinearCollisionTransfer.restrictedCollision`, `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.MixedSupport.Projection` and `OAI.PerfectCompleteness.MixedSupport.Slot` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.CutChildGrouping.Raw`, `OAI.PerfectCompleteness.FiniteProduct.law`, `OAI.PerfectCompleteness.TreeSourceSpaces.Domain`, `OAI.PerfectCompleteness.TreeSourceSpaces.H`, `OAI.PerfectCompleteness.TreeSourceSpaces.childSlots` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.uniform` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.ParentForm`, `OAI.PerfectCompleteness.ChildBlockCardinality.bound`, `OAI.PerfectCompleteness.ChildCallNumbering.Raw`, `OAI.PerfectCompleteness.ChildCallNumbering.rawFintype`, `OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty`, `OAI.PerfectCompleteness.ChildCallNumberingLaws.replacementLaws` and `OAI.PerfectCompleteness.ChildUnmarkedSpace.space` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.SparseReplacement.markedLaw` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedSourceGlobalCollision.mean_local_le` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/ChildFiniteCallCollisionTransfer.lean (declaration OAI.PerfectCompleteness.ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full)

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
import Definitions.Def_OAIQ252P007
import Definitions.Def_OAIQ252P011

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildFiniteCallCollisionTransfer

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  {Z : Fin (branch n) → Type*} [∀ i, Fintype (Z i)]

theorem marked_restricted_le_uniform_full
    (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection
      (childSlots slots i s k) (projected i z s k))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (F₀ F₁ : CutChildGrouping.Raw (C := C) slots rows →
      Option (ChildBilinearCollisionTransfer.ParentForm slots)) :
    (SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform
          (ChildCallNumbering.Raw (C := C) rows (childSlots slots i)))
        (ChildCallNumberingLaws.replacementLaws (C := C) rows (childSlots slots)
          projected p choiceLaw) β hβ hβ'.le).probability
      (fun z => BilinearCollisionTransfer.restrictedCollision
        (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) ≤
      (FiniteProduct.law (fun i => FiniteDistribution.uniform
        (ChildCallNumbering.Raw (C := C) rows (childSlots slots i)))).probability
          (fun x => BilinearCollisionTransfer.fullCollision (F₀ x) (F₁ x)) +
        2 * (β * (ChildBlockCardinality.bound branch n t (Fintype.card C) rows : ℝ) /
          (1 - β)) +
        Real.sqrt ((1 + β ^ 2 *
          ((ChildBlockCardinality.bound branch n t (Fintype.card C) rows : ℝ) - 1)) ^
            branch n - 1) / 2 := by
  sorry

end
end PerfectCompleteness.ChildFiniteCallCollisionTransfer

end

end OAI
end
