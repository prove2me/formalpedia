-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_map_finiteEvaluation_eq_of_integral_tendsto
-- name    : MarkovProcess.Kernel.map_finiteEvaluation_eq_of_integral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:15:39.799747+00:00
-- url     : https://prove2.me/theorems/7486fcaf-70b5-4ae1-ab0d-41a66b723744
-- title:
--   Finite-dimensional law equality passes to time limits
-- statement:
--   Equality of finite-dimensional laws passes from approximating time families to their limit
--   once the comparison kernels have the corresponding compactly-supported-test convergence.
--
--   The convergence premise is deliberately stated at precisely the analytic seam: it says nothing
--   about a Markov property and is exactly the weak/vague continuity of the candidate finite-time
--   laws needed by the proof.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/AllTimeFiniteMarginals.lean#L155-L212

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_PositiveC0OperatorMeasure
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_AllTimeFiniteMarginals
import Definitions.Def_MarkovProcess_Trajectory_Basic
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Arbitrary-time finite marginals of continuous-path trajectories

This file develops the simultaneous rational approximation needed to pass from the already
identified rational finite-dimensional distributions to finite families of arbitrary
nonnegative real times.  It proves the path-side dominated-convergence argument, identifies every
rational approximating law with the existing finite-set kernel, and reduces the desired equality
to compactly-supported-test convergence of those finite-set kernels.

The remaining Feller analytic statement is not claimed here: one must still prove that the
recursively composed finite-time kernels have that convergence under simultaneous convergence of
their strictly ordered time coordinates.  No continuous-time Markov or Hunt property is assumed
or asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal


noncomputable section
















variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]

theorem MarkovProcess.Kernel.map_finiteEvaluation_eq_of_integral_tendsto
    {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    (K : Kernel β (ContinuousPath α)) (hK : IsMarkovKernel K)
    (Lseq : ℕ → Kernel β (ι → α)) (L : Kernel β (ι → α))
    (hL : IsMarkovKernel L) (τ : ι → NNReal) (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i)))
    (hlaw : ∀ k, K.map (ContinuousPath.finiteEvaluation (q k)) = Lseq k)
    (hfinite : ∀ (x : β) (f : CompactlySupportedContinuousMap (ι → α) ℝ),
      Tendsto (fun k ↦ ∫ y, f y ∂Lseq k x) atTop (nhds (∫ y, f y ∂L x))) :
    K.map (ContinuousPath.finiteEvaluation τ) = L := by sorry
