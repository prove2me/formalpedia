-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_FixedSourcePhysicalHigh_probability_square_le_collision
-- name    : OAI.PerfectCompleteness.FixedSourcePhysicalHigh.probability_square_le_collision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:03:08.421547+00:00
-- url     : https://prove2.me/theorems/a19a9650-efae-43af-bcac-19f789ba6f40
-- title:
--   OAI.PerfectCompleteness.FixedSourcePhysicalHigh.probability_square_le_collision: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.FixedSourcePhysicalHigh.probability_square_le_collision` of [lean/OAI/Computability/PerfectCompleteness/Reduction/FixedSourcePhysicalHighLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Reduction/FixedSourcePhysicalHighLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.FixedSourcePhysicalHigh`, with `open scoped Classical BigOperators`, `open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open UniqueGamesTheorem.Foundations.Games`):
--
--   ```lean
--   theorem probability_square_le_collision :
--       probability parameters outside placeholder clauses designated upper pDown hproper d hnode A cut
--           exterior σ useful density threshold ^ 2 ≤
--         (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
--           (fun direction => (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
--             (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
--               (HierarchicalAllDecoderTables.upperTableLaw
--                 (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q)
--                 upper (height + 1) σ (useful q) adviceRows density).expectation (fun table =>
--                   (tagLaw parameters).expectation (fun tag =>
--                     SourceQuestionPhysicalHigh.collision ((Nodes.path upper).append pDown) outside placeholder
--                       clauses designated q tag.1 tag.2 upper (height + 1) d
--                       (FixedLowerRawCollision.branchPositive parameters) A exterior direction
--                       (cutoff parameters.plan hδ) table))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.RecursiveSpaces.Slots`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.expectation` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.BucketSampler.Direction`, `OAI.PerfectCompleteness.BucketSampler.F2`, `OAI.PerfectCompleteness.DescendantSpaces.Path`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes`, `OAI.PerfectCompleteness.KeyStrategy.Strategy`, `OAI.PerfectCompleteness.MixedSupport.Slot`, `OAI.PerfectCompleteness.SourceProjectedTag.Flags` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Block`, `OAI.PerfectCompleteness.HierarchicalFrozenTables.LowerNodes`, `OAI.PerfectCompleteness.HierarchicalLeftDecoder.LowerNode`, `OAI.PerfectCompleteness.HierarchicalMatrixTable.Background`, `OAI.PerfectCompleteness.NodeEmbedding.NumberedDomain`, `OAI.PerfectCompleteness.NodeEmbedding.RowSpace`, `OAI.PerfectCompleteness.OwnInputReference.Cut`, `OAI.PerfectCompleteness.PreliminarySampler.Questions`, `OAI.PerfectCompleteness.PreliminarySampler.questionsLaw`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsDecidableEq`, `OAI.PerfectCompleteness.RecursiveSpaces.slotsFintype`, `OAI.PerfectCompleteness.SourceClause.NormalizedClause`, `OAI.PerfectCompleteness.TreeCanonical.locationCount`, `OAI.PerfectCompleteness.DescendantSpaces.Path.append`, `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.path` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.uniform` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.ManyGoodRows.RowMap` (definitions bundle `OAIQ252P004` of this split); `OAI.PerfectCompleteness.CleanPhysicalReplay.Exterior`, `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.Background`, `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.Input`, `OAI.PerfectCompleteness.HierarchicalDecoderTables.Advice`, `OAI.PerfectCompleteness.HierarchicalFrozenTables.QuotientMatrix`, `OAI.PerfectCompleteness.HierarchicalFrozenTables.knownRows` and `OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.FixedRows.rows`, `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.UpperAnswer`, `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.upperDualFintype` and `OAI.PerfectCompleteness.FixedRows.Plan` (definitions bundle `OAIQ252P008` of this split); `OAI.PerfectCompleteness.FixedRows.repeats`, `OAI.PerfectCompleteness.ProjectedLowerFiber.lower`, `OAI.PerfectCompleteness.SourceProjectedTag.Tag`, `OAI.PerfectCompleteness.SourceQuestionKernelJoint.ChoiceTuple` and `OAI.PerfectCompleteness.SourceQuestionPositionSplit.ChildPositions` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.FixedRows.cutoff` and `OAI.PerfectCompleteness.FixedRows.sourceLength` (definitions bundle `OAIQ252P013` of this split); `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype` (definitions bundle `OAIQ252P015` of this split); `OAI.PerfectCompleteness.FixedParameters.Parameters` and `OAI.PerfectCompleteness.FixedParameters.branch` (definitions bundle `OAIQ252P016` of this split); `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.upperTableLaw`, `OAI.PerfectCompleteness.SourceQuestionLowerForms.slots` and `OAI.PerfectCompleteness.SourceQuestionPhysicalHigh.collision` (definitions bundle `OAIQ252P017` of this split); `OAI.PerfectCompleteness.FixedLowerRawCollision.branchPositive`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.Questions`, `OAI.PerfectCompleteness.FixedSourcePhysicalHigh.directionNonempty`, `OAI.PerfectCompleteness.FixedSourcePhysicalHigh.probability` and `OAI.PerfectCompleteness.FixedSourcePhysicalHigh.tagLaw` (definitions bundle `OAIQ252P018` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedStoppedHighBound.directionMean_square_le` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Reduction/FixedSourcePhysicalHighLemmas.lean (declaration OAI.PerfectCompleteness.FixedSourcePhysicalHigh.probability_square_le_collision)

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

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourcePhysicalHigh

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (pDown : Path (branch parameters) (Nodes.height upper) (height + 1))
  (hproper : height + 1 < Nodes.height upper)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode ((Nodes.path upper).append pDown) =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper (height + 1) d))
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    ((Nodes.path upper).append pDown) outside placeholder)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q)
      upper (height + 1) bg → Prop)
  (density threshold : ℝ)

local instance rowSpaceFintype_r3eb86d_1 (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r3eb86d_1 (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  LeftDecoder.dualFintype
    (V := NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper)
attribute [local instance] OAI.PerfectCompleteness.FixedSourcePhysicalHigh.directionNonempty
theorem probability_square_le_collision :
    probability parameters outside placeholder clauses designated upper pDown hproper d hnode A cut
        exterior σ useful density threshold ^ 2 ≤
      (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
        (fun direction => (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
          (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
            (HierarchicalAllDecoderTables.upperTableLaw
              (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q)
              upper (height + 1) σ (useful q) adviceRows density).expectation (fun table =>
                (tagLaw parameters).expectation (fun tag =>
                  SourceQuestionPhysicalHigh.collision ((Nodes.path upper).append pDown) outside placeholder
                    clauses designated q tag.1 tag.2 upper (height + 1) d
                    (FixedLowerRawCollision.branchPositive parameters) A exterior direction
                    (cutoff parameters.plan hδ) table)))) := by
  sorry

end
end PerfectCompleteness.FixedSourcePhysicalHigh

end

end OAI
end
