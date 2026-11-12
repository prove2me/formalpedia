-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedUsefulMass_joint_probability_eq_physical
-- name    : OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:04:10.172442+00:00
-- url     : https://prove2.me/theorems/2cf2f9e4-c527-4b70-afcb-4cd10022627a
-- title:
--   OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical` of [lean/OAI/Computability/PerfectCompleteness/Reduction/FixedStoppedUsefulMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Reduction/FixedStoppedUsefulMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.FixedStoppedUsefulMass`, with `open scoped Classical`, `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open UniqueGamesTheorem.Foundations.Games`):
--
--   ```lean
--   theorem joint_probability_eq_physical :
--       (originalLaw parameters i j hij input designated strategy).probability
--         (HierarchicalUsefulFamily.jointEvent
--           (experiment parameters i j hij input designated strategy)
--           (upperEvent parameters i j hij input designated strategy)) =
--       (physicalLaw parameters i j hij input designated).probability (fun sample =>
--         StoppedSharedEvents.pair (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
--           (fun k _ => FixedParameters.branch_pos parameters k) i j
--           (physicalRecord parameters i j hij input designated sample))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.BinaryLanguage.totalRename`, `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.UniqueGamesTheorem.Foundations.Target.Clause`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` and `OAI.UniqueGamesTheorem.Foundations.Target.Formula` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.BucketSampler.F2`, `OAI.PerfectCompleteness.GeometricCutSplit.Prefix`, `OAI.PerfectCompleteness.MixedSupport.Slot`, `OAI.PerfectCompleteness.SourceProjectedTag.Flags` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.CanonicalDirections.Tuple`, `OAI.PerfectCompleteness.PrefixTests.LevelDirection`, `OAI.PerfectCompleteness.PreliminarySampler.Questions`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsDecidableEq`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsFintype`, `OAI.PerfectCompleteness.WholeArraySampler.Tape` and `OAI.PerfectCompleteness.WholeArraySampler.tapeFintype` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.GeometricCutSplit.prefixDepthFintype` (definitions bundle `OAIQ252P005` of this split); `OAI.PerfectCompleteness.CleanPhysicalReplay.Exterior`, `OAI.PerfectCompleteness.CutSlotAssembly.fill`, `OAI.PerfectCompleteness.SourceChildKernel.Raw`, `OAI.PerfectCompleteness.SourceChildKernel.rawFintype`, `OAI.PerfectCompleteness.WholeCutCalls.Index` and `OAI.PerfectCompleteness.WholeCutCalls.indexFintype` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.FixedRows.rows` and `OAI.PerfectCompleteness.FixedRows.Plan` (definitions bundle `OAIQ252P008` of this split); `OAI.PerfectCompleteness.FixedRows.repeats`, `OAI.PerfectCompleteness.PCPSource.normalizedFormula`, `OAI.PerfectCompleteness.SourceProjectedTag.Tag`, `OAI.PerfectCompleteness.SourceProjectedTag.originalSlots`, `OAI.PerfectCompleteness.SourceQuestionKernelJoint.ChoiceTuple`, `OAI.PerfectCompleteness.SourceQuestionPositionSplit.ChildPositions` and `OAI.PerfectCompleteness.WholeArrayInteriorOwnInputLaw.fullPath` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.FixedRows.sourceLength` (definitions bundle `OAIQ252P013` of this split); `OAI.PerfectCompleteness.HierarchicalUsefulFamily.jointEvent` and `OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype` (definitions bundle `OAIQ252P015` of this split); `OAI.PerfectCompleteness.FixedParameters.Parameters`, `OAI.PerfectCompleteness.FixedParameters.branch` and `OAI.PerfectCompleteness.FixedParameters.branch_pos` (definitions bundle `OAIQ252P016` of this split); `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.Sample`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.Inner`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.PhysicalBase`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.PhysicalRaw`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.PhysicalSample`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.baseTag`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.cut`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.cutQuestions`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.lower`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.nativeSlots`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.projectedSlots`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.stoppedPath`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.upper`, `OAI.PerfectCompleteness.StoppedProjectedGlobalLaw.Outer`, `OAI.PerfectCompleteness.StoppedProjectedPhysicalLaw.Outer` and `OAI.PerfectCompleteness.StoppedSharedEvents.pair` (definitions bundle `OAIQ252P017` of this split); `OAI.PerfectCompleteness.FixedPreliminaryGame.Strategy`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.OriginalSample`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.PhysicalSample`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.clauses`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.experiment`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.originalLaw`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.physicalLaw`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.physicalRecord` and `OAI.PerfectCompleteness.FixedStoppedUsefulMass.upperEvent` (definitions bundle `OAIQ252P018` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedStoppedUsefulMass.useful_probability_ge_of_reserve` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Reduction/FixedStoppedUsefulMass.lean (declaration OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical)

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

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedUsefulMass

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

variable (designated : Fin (FixedParameters.branch parameters i.val) →
  Slots (FixedParameters.branch parameters) i.val)

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

theorem joint_probability_eq_physical :
    (originalLaw parameters i j hij input designated strategy).probability
      (HierarchicalUsefulFamily.jointEvent
        (experiment parameters i j hij input designated strategy)
        (upperEvent parameters i j hij input designated strategy)) =
    (physicalLaw parameters i j hij input designated).probability (fun sample =>
      StoppedSharedEvents.pair (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k) i j
        (physicalRecord parameters i j hij input designated sample)) := by
  sorry

end
end PerfectCompleteness.FixedStoppedUsefulMass

end

end OAI
end
