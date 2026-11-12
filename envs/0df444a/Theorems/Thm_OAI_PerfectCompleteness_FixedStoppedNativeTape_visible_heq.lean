-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedNativeTape_visible_heq
-- name    : OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:03:47.341667+00:00
-- url     : https://prove2.me/theorems/18539b6c-95da-44e1-8125-24017bb0e1fd
-- title:
--   OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq` of [lean/OAI/Computability/PerfectCompleteness/Machines/FixedStoppedNativeTape.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Machines/FixedStoppedNativeTape.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.FixedStoppedNativeTape`, with `open scoped Classical`, `open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays`, `open FixedStoppedPhysicalLaw (clauses designated)`, `open FixedStoppedNativeProjection (physicalSample innerTag path childSample)`):
--
--   ```lean
--   theorem visible_heq :
--       HEq (rawRead parameters i j hij input sample).2.2.2.2
--         (CleanPhysicalProjectedMeeting.visible S
--           (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
--           sample.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.BinaryLanguage.totalRename`, `OAI.PerfectCompleteness.TreeSourceSpaces.F2`, `OAI.UniqueGamesTheorem.Foundations.Target.Clause`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2` and `OAI.UniqueGamesTheorem.Foundations.Target.Formula` (definitions bundle `OAIQ252P000` of this split); `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.F2`, `OAI.PerfectCompleteness.OwnInputReference.F2` and `OAI.PerfectCompleteness.HierarchicalArrays.Nodes.height` (definitions bundle `OAIQ252P001` of this split); `OAI.PerfectCompleteness.HierarchicalArrays.Block`, `OAI.PerfectCompleteness.OwnInputReference.Exterior` and `OAI.PerfectCompleteness.OwnInputReference.UpperVector` (definitions bundle `OAIQ252P003` of this split); `OAI.PerfectCompleteness.CleanDecoderRate.Sample`, `OAI.PerfectCompleteness.CleanNativeReplay.rightSlots`, `OAI.PerfectCompleteness.HiddenBucketBias.HiddenTape`, `OAI.PerfectCompleteness.HiddenBucketBias.VisibleTape` and `OAI.PerfectCompleteness.CleanDecoderRate.Setup` (definitions bundle `OAIQ252P007` of this split); `OAI.PerfectCompleteness.FixedRows.rows`, `OAI.PerfectCompleteness.OwnInputReference.ScalarSample` and `OAI.PerfectCompleteness.FixedRows.Plan` (definitions bundle `OAIQ252P008` of this split); `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.lower`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.visible`, `OAI.PerfectCompleteness.FixedRows.repeats`, `OAI.PerfectCompleteness.OwnInputReference.RawSample` and `OAI.PerfectCompleteness.PCPSource.normalizedFormula` (definitions bundle `OAIQ252P012` of this split); `OAI.PerfectCompleteness.FixedRows.sourceLength` (definitions bundle `OAIQ252P013` of this split); `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.Advice` (definitions bundle `OAIQ252P015` of this split); `OAI.PerfectCompleteness.FixedParameters.Parameters`, `OAI.PerfectCompleteness.FixedParameters.branch` and `OAI.PerfectCompleteness.PCPSource.clauseCount_neZero` (definitions bundle `OAIQ252P016` of this split); `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.RawSample`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.Inner`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.cut`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.lower`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.projectedSlots`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.upper` and `OAI.PerfectCompleteness.StoppedProjectedPhysicalAdvice.Outer` (definitions bundle `OAIQ252P017` of this split); `OAI.PerfectCompleteness.FixedStoppedDecoderContext.advice`, `OAI.PerfectCompleteness.FixedStoppedDecoderContext.lowerIndex`, `OAI.PerfectCompleteness.FixedStoppedDecoderContext.upperNode`, `OAI.PerfectCompleteness.FixedStoppedNativeLaw.Context`, `OAI.PerfectCompleteness.FixedStoppedNativeLaw.Sample`, `OAI.PerfectCompleteness.FixedStoppedNativeLaw.setup`, `OAI.PerfectCompleteness.FixedStoppedNativeTape.rawRead`, `OAI.PerfectCompleteness.FixedStoppedPhysicalLaw.clauses` and `OAI.PerfectCompleteness.FixedStoppedPhysicalLaw.designated` (definitions bundle `OAIQ252P018` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.meeting_probability_eq_expectedMeeting` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Machines/FixedStoppedNativeTape.lean (declaration OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq)

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

attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedNativeTape

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open FixedStoppedPhysicalLaw (clauses designated)
open FixedStoppedNativeProjection (physicalSample innerTag path childSample)

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (sample : FixedStoppedNativeLaw.Sample parameters i j hij input)

local notation "R" => FixedRows.rows parameters.plan
local notation "T" => FixedRows.repeats parameters.plan
local notation "C" => clauses input
local notation "D" => designated parameters i
local notation "hu" => Nat.succ_le_of_lt j.isLt
local notation "P" => physicalSample parameters i j hij input sample
local notation "K" => innerTag parameters i j hij input sample
local notation "S" => FixedStoppedNativeLaw.setup parameters i j hij input (Sigma.fst sample)

theorem visible_heq :
    HEq (rawRead parameters i j hij input sample).2.2.2.2
      (CleanPhysicalProjectedMeeting.visible S
        (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
        sample.2) := by
  sorry

end
end PerfectCompleteness.FixedStoppedNativeTape

end

end OAI
end
