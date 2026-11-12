-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_HierarchicalAdviceFamily_prediction_difference
-- name    : OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction_difference
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:49:31.374016+00:00
-- url     : https://prove2.me/theorems/2873bcd1-bfa3-403f-a620-c41104997823
-- title:
--   OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction_difference: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction_difference` of [lean/OAI/Computability/PerfectCompleteness/Foundations/HierarchicalAdviceExperimentLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/HierarchicalAdviceExperimentLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.HierarchicalAdviceFamily`, with `open scoped Classical`, `open TreeSourceSpaces HierarchicalArrays`, `open UniqueGamesTheorem.Foundations.Games`, `open UniqueGamesTheorem.Appendix.RankLevelFilter`, `open UniqueGamesTheorem.Fourier.MatrixLevelBridge`):
--
--   ```lean
--   theorem prediction_difference (κ : ℝ) (hκ : 0 ≤ κ) (outer : FiniteDistribution O)
--       (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
--       (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))
--       (ℓ : Nat) (hdim : ∀ o, rows (Nodes.height (S o).upper) ≤ ℓ)
--       (r : Nat) (ρ η v : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
--       (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
--       (hmean : 2 * η ≤ (backgroundLaw S outer backgrounds).expectation
--         (fun b => PartialTableInverse.nonzeroAgreement (table S κ b)))
--       (hv : 0 ≤ v) (hsmall : v ≤ ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) / 16)
--       (hvariation : ((originalLaw S outer r).pushforward (observe S r)).totalVariation
--         ((referenceLaw S outer backgrounds r).pushforward (referenceObserve S r)) ≤ v) :
--       κ * ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) / 4 ≤
--         (originalLaw S outer r).probability (prediction S κ r ρ) -
--         (κ * ρ / 4) * (originalLaw S outer r).probability
--           (fun x => J S κ r ρ (observe S r x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2`, `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.expectation` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height`, `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.node` and `OAI.UniqueGamesTheorem.Fourier.MatrixLevelBridge.levelCutoffConstant` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Block`, `OAI.PerfectCompleteness.NodeEmbedding.NumberedDomain`, `OAI.PerfectCompleteness.NodeEmbedding.RowSpace` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.ManyGoodRows.RowMap` (definitions bundle `OAIQ252P004` of this split); `OAI.PerfectCompleteness.PartialTableInverse.nonzeroAgreement` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.totalVariation` (definitions bundle `OAIQ252P006` of this split); `OAI.PerfectCompleteness.HierarchicalFrozenTables.knownRows` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Advice`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Background`, `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Experiment`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Background`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.OriginalSample`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Row`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Value`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.backgroundFiberFintype`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.backgroundLaw` and `OAI.PerfectCompleteness.HierarchicalAdviceFamily.originalLaw` (definitions bundle `OAIQ252P011` of this split); `OAI.PerfectCompleteness.HierarchicalAdviceExperiment.Coarse`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Input`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.J`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.Observation`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.ReferenceSample`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.coarseFintype`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.inputFintype`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.observe`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.referenceLaw`, `OAI.PerfectCompleteness.HierarchicalAdviceFamily.referenceObserve` and `OAI.PerfectCompleteness.HierarchicalAdviceFamily.table` (definitions bundle `OAIQ252P015` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedStoppedInverseBound.expectedMeeting_ge_gamma` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/HierarchicalAdviceExperimentLemmas.lean (declaration OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction_difference)

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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Definitions.Def_OAIQ252P015

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PerfectCompleteness.HierarchicalAdviceFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Fourier.MatrixLevelBridge

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.backgroundFiberFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.inputFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.valueFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.coarseFintype
theorem prediction_difference (κ : ℝ) (hκ : 0 ≤ κ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))
    (ℓ : Nat) (hdim : ∀ o, rows (Nodes.height (S o).upper) ≤ ℓ)
    (r : Nat) (ρ η v : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ (backgroundLaw S outer backgrounds).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (table S κ b)))
    (hv : 0 ≤ v) (hsmall : v ≤ ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) / 16)
    (hvariation : ((originalLaw S outer r).pushforward (observe S r)).totalVariation
      ((referenceLaw S outer backgrounds r).pushforward (referenceObserve S r)) ≤ v) :
    κ * ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) / 4 ≤
      (originalLaw S outer r).probability (prediction S κ r ρ) -
      (κ * ρ / 4) * (originalLaw S outer r).probability
        (fun x => J S κ r ρ (observe S r x)) := by
  sorry

end
end PerfectCompleteness.HierarchicalAdviceFamily

end OAI
end
