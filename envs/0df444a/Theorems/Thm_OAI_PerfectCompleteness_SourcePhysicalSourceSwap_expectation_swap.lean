-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_SourcePhysicalSourceSwap_expectation_swap
-- name    : OAI.PerfectCompleteness.SourcePhysicalSourceSwap.expectation_swap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:57:43.432783+00:00
-- url     : https://prove2.me/theorems/5c5777e5-9894-4c01-b880-5fdfe504c3af
-- title:
--   OAI.PerfectCompleteness.SourcePhysicalSourceSwap.expectation_swap: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.SourcePhysicalSourceSwap.expectation_swap` of [lean/OAI/Computability/PerfectCompleteness/Foundations/SourcePhysicalSourceSwapLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/SourcePhysicalSourceSwapLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.SourcePhysicalSourceSwap`, with `open scoped Classical`, `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open UniqueGamesTheorem.Foundations.Games`):
--
--   ```lean
--   theorem expectation_swap
--       (flag : Fin (branch h) → FiniteDistribution Bool)
--       (value : (questions : Questions (branch := branch) (root := root) (t := t) (m := m)) →
--         Positions (branch := branch) (h := h) (t := t) →
--         SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p questions →
--         Raw clauses rows repeats p designated → ℝ) :
--       (PreliminarySampler.questionsLaw
--         (branch := branch) (n := root) (t := t) (m := m)).expectation
--           (fun questions => (SourceProjectedTag.positionLaw
--             (branch := branch) (n := h) (t := t)).expectation (fun positions =>
--               (SourcePhysicalWholeLaw.rawLaw rows repeats p
--                 (sourceSlots clauses (PreliminarySampler.endpoints questions))
--                 (sourceSlots clauses (PreliminarySampler.endpoints
--                   (SourceQuestionCutSplit.restrict p questions)))
--                 clauses designated flag (SourceQuestionKernelJoint.sources designated
--                   (SourceQuestionCutSplit.restrict p questions) positions)).expectation
--                     (fun sample => value questions positions sample.1 sample.2))) =
--         (FiniteDistribution.uniform (SourceQuestionCutSplit.OutsideQuestions p t m)).expectation
--           (fun external => (FiniteDistribution.uniform
--             (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external)).expectation
--               (fun exterior => (SourceChildKernel.originalLaw
--                 (C := WholeCutCalls.Index rows repeats p) (t := t)
--                 rows clauses designated flag).expectation (fun sample =>
--                   value (SourceQuestionCutSplit.join p
--                       (SourceQuestionRawSwap.insideQuestions rows clauses designated sample) external)
--                     (SourceQuestionRawSwap.positions rows clauses designated sample)
--                     (joinedExterior clauses rows repeats p
--                       (SourceQuestionRawSwap.insideQuestions rows clauses designated sample)
--                       external exterior)
--                     (SourceQuestionRawSwap.raw rows clauses designated sample))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.expectation` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.DescendantSpaces.Path` and `OAI.PerfectCompleteness.MixedSupport.Slot` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.sourceSlots`, `OAI.PerfectCompleteness.PreliminarySampler.Questions`, `OAI.PerfectCompleteness.PreliminarySampler.endpoints`, `OAI.PerfectCompleteness.PreliminarySampler.questionsLaw`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsDecidableEq`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsFintype`, `OAI.PerfectCompleteness.SourceClause.NormalizedClause`, `OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.uniform` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.CleanPhysicalReplay.Exterior`, `OAI.PerfectCompleteness.CutSlotAssembly.fill`, `OAI.PerfectCompleteness.SourceChildKernel.Raw`, `OAI.PerfectCompleteness.SourceChildKernel.Sample`, `OAI.PerfectCompleteness.SourceChildKernel.originalLaw`, `OAI.PerfectCompleteness.SourceChildKernel.rawFintype`, `OAI.PerfectCompleteness.SourceChildKernel.sampleFintype`, `OAI.PerfectCompleteness.SourceQuestionCutSplit.OutsideLeaf`, `OAI.PerfectCompleteness.WholeCutCalls.Index` and `OAI.PerfectCompleteness.WholeCutCalls.indexFintype` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.SourceQuestionCutSplit.OutsideQuestions`, `OAI.PerfectCompleteness.SourceQuestionCutSplit.join`, `OAI.PerfectCompleteness.SourceQuestionCutSplit.restrict`, `OAI.PerfectCompleteness.SourceQuestionKernelJoint.ChoiceTuple`, `OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources`, `OAI.PerfectCompleteness.SourceQuestionPositionSplit.ChildPositions` and `OAI.PerfectCompleteness.SourceQuestionRawSwap.raw` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype` and `OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty` (definitions bundle `OAIQ252P015` of this split); `OAI.PerfectCompleteness.SourcePhysicalExteriorSwap.ActualExterior`, `OAI.PerfectCompleteness.SourcePhysicalExteriorSwap.CanonicalExterior`, `OAI.PerfectCompleteness.SourcePhysicalExteriorSwap.canonicalSlots`, `OAI.PerfectCompleteness.SourcePhysicalSourceSwap.Positions`, `OAI.PerfectCompleteness.SourcePhysicalSourceSwap.Questions`, `OAI.PerfectCompleteness.SourcePhysicalSourceSwap.Raw`, `OAI.PerfectCompleteness.SourcePhysicalSourceSwap.joinedExterior`, `OAI.PerfectCompleteness.SourcePhysicalWholeLaw.Raw`, `OAI.PerfectCompleteness.SourcePhysicalWholeLaw.rawLaw`, `OAI.PerfectCompleteness.SourceProjectedTag.positionLaw`, `OAI.PerfectCompleteness.SourceQuestionRawSwap.insideQuestions` and `OAI.PerfectCompleteness.SourceQuestionRawSwap.positions` (definitions bundle `OAIQ252P017` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.physical_expectation_eq_expectedMeeting` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/SourcePhysicalSourceSwapLemmas.lean (declaration OAI.PerfectCompleteness.SourcePhysicalSourceSwap.expectation_swap)

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

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalSourceSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (designated : Fin (branch h) → Slots branch h)

theorem expectation_swap
    (flag : Fin (branch h) → FiniteDistribution Bool)
    (value : (questions : Questions (branch := branch) (root := root) (t := t) (m := m)) →
      Positions (branch := branch) (h := h) (t := t) →
      SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p questions →
      Raw clauses rows repeats p designated → ℝ) :
    (PreliminarySampler.questionsLaw
      (branch := branch) (n := root) (t := t) (m := m)).expectation
        (fun questions => (SourceProjectedTag.positionLaw
          (branch := branch) (n := h) (t := t)).expectation (fun positions =>
            (SourcePhysicalWholeLaw.rawLaw rows repeats p
              (sourceSlots clauses (PreliminarySampler.endpoints questions))
              (sourceSlots clauses (PreliminarySampler.endpoints
                (SourceQuestionCutSplit.restrict p questions)))
              clauses designated flag (SourceQuestionKernelJoint.sources designated
                (SourceQuestionCutSplit.restrict p questions) positions)).expectation
                  (fun sample => value questions positions sample.1 sample.2))) =
      (FiniteDistribution.uniform (SourceQuestionCutSplit.OutsideQuestions p t m)).expectation
        (fun external => (FiniteDistribution.uniform
          (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external)).expectation
            (fun exterior => (SourceChildKernel.originalLaw
              (C := WholeCutCalls.Index rows repeats p) (t := t)
              rows clauses designated flag).expectation (fun sample =>
                value (SourceQuestionCutSplit.join p
                    (SourceQuestionRawSwap.insideQuestions rows clauses designated sample) external)
                  (SourceQuestionRawSwap.positions rows clauses designated sample)
                  (joinedExterior clauses rows repeats p
                    (SourceQuestionRawSwap.insideQuestions rows clauses designated sample)
                    external exterior)
                  (SourceQuestionRawSwap.raw rows clauses designated sample)))) := by
  sorry

end
end PerfectCompleteness.SourcePhysicalSourceSwap

end

end OAI
end
