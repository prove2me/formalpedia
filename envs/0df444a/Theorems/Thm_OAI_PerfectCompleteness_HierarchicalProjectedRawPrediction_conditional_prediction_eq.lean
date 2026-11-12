-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_HierarchicalProjectedRawPrediction_conditional_prediction_eq
-- name    : OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:54:50.948714+00:00
-- url     : https://prove2.me/theorems/80476914-0952-4d6f-9611-d0d4a41830cc
-- title:
--   OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq` of [lean/OAI/Computability/PerfectCompleteness/Foundations/HierarchicalProjectedSliceLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/HierarchicalProjectedSliceLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction`, with `open scoped Classical TensorProduct`, `open TreeSourceSpaces HierarchicalArrays`, `open UniqueGamesTheorem.Foundations.Games`, `open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)`):
--
--   ```lean
--   theorem conditional_prediction_eq (a : Block rows lower)
--       (externalLaw : FiniteDistribution (OwnInputReference.Exterior projectedSlots rows upper lower))
--       (v : Visible projectedSlots rows upper lower A repeats cut)
--       (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
--         A repeats cut v)
--       (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
--         A repeats cut v T = true)
--       (positive : 0 <
--         (OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).probability
--           (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)) :
--       ((OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).condition
--         (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)
--         positive).probability
--           (rawPrediction originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
--             A repeats cut a) =
--         RightDecoderWitness.conditionalMatch projectedSlots rows upper lower (LinearMap.ker A) a repeats cut σ
--           (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
--             (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) v)
--           (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
--             A repeats cut v hgood)
--           (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
--             A repeats cut v hgood hne)
--           (nativeCorrection originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
--             A repeats cut v hgood)
--           (visibleOffset originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
--             A repeats cut v hgood)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Nodes`, `OAI.PerfectCompleteness.KeyStrategy.Strategy`, `OAI.PerfectCompleteness.MixedSupport.Projection`, `OAI.PerfectCompleteness.MixedSupport.Slot`, `OAI.PerfectCompleteness.OwnInputReference.F2` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.RightDecoderWitness.F2` (definitions bundle `OAIQ252P002` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Arrays`, `OAI.PerfectCompleteness.HierarchicalArrays.Block`, `OAI.PerfectCompleteness.OwnInputReference.Cut`, `OAI.PerfectCompleteness.OwnInputReference.Exterior`, `OAI.PerfectCompleteness.OwnInputReference.UpperVector` and `OAI.PerfectCompleteness.TreeCanonical.locationCount` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.ManyGoodRows.RowMap` (definitions bundle `OAIQ252P004` of this split); `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.condition` (definitions bundle `OAIQ252P006` of this split); `OAI.PerfectCompleteness.OwnInputReference.readInput` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.OwnInputRawAssembly.scalarEval` and `OAI.PerfectCompleteness.OwnInputReference.ScalarSample` (definitions bundle `OAIQ252P008` of this split); `OAI.PerfectCompleteness.HierarchicalProjectedSlice.HiddenTensor` and `OAI.PerfectCompleteness.OwnInputReference.exteriorFintype` (definitions bundle `OAIQ252P011` of this split); `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.Visible` and `OAI.PerfectCompleteness.OwnInputReference.RawSample` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.RightDecoderWitness.conditionalMatch` (definitions bundle `OAIQ252P015` of this split); `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.VisibleGood`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.columnSpace`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.given`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.nativeCorrection`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rawPrediction`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.target`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.tensorJ`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.visibleOffset`, `OAI.PerfectCompleteness.OwnInputReference.rawLaw` and `OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype` (definitions bundle `OAIQ252P017` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.expectedMeeting_ge_prediction_difference` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/HierarchicalProjectedSliceLemmas.lean (declaration OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq)

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
import Definitions.Def_OAIQ252P017

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PerfectCompleteness.HierarchicalProjectedRawPrediction

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (rows : Nat → Nat) (upper lower : Nodes branch n) (lowerLevel : Nat)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rowSpaceFintype
local instance valueFintype_redb730_1 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
theorem conditional_prediction_eq (a : Block rows lower)
    (externalLaw : FiniteDistribution (OwnInputReference.Exterior projectedSlots rows upper lower))
    (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true)
    (positive : 0 <
      (OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).probability
        (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)) :
    ((OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).condition
      (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)
      positive).probability
        (rawPrediction originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut a) =
      RightDecoderWitness.conditionalMatch projectedSlots rows upper lower (LinearMap.ker A) a repeats cut σ
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) v)
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne)
        (nativeCorrection originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (visibleOffset originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) := by
  sorry

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
end
