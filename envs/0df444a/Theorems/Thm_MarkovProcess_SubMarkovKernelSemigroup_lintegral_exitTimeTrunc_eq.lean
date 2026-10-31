-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_lintegral_exitTimeTrunc_eq
-- name    : MarkovProcess.SubMarkovKernelSemigroup.lintegral_exitTimeTrunc_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:13.427471+00:00
-- url     : https://prove2.me/theorems/7cfc04ee-5d76-42fb-9301-396f40b3b217
-- title:
--   MarkovProcess: lintegral_exitTimeTrunc_eq
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The expected exit time, untruncated

The expected exit time bound of `Trajectory/DynkinStopping.lean` is stated for the exit time
truncated at a deterministic horizon `K`, uniformly in `K`.  This file removes the truncation by
monotone convergence: under the same hypotheses (`L f ≤ -1` on the open set `U`, `f ≥ m`),

  `E_x τ_U ≤ f x - m`  (`IsFellerKernelSemigroup.lintegral_exitTime_le`),

as an `ℝ≥0∞`-valued integral of the `ℝ≥0∞`-valued exit time, so in particular the exit time from
`U` is almost surely finite from every starting point (`ae_exitTime_lt_top`).

It also records that the truncated exit time of `Path/ExitTime.lean` is the generic truncation
`StoppingTime.truncTime` of `Trajectory/StoppingLtTop.lean` applied to `exitTimeTop`
(`ContinuousPath.exitTimeTrunc_eq_truncTime`), and the monotone limit
`ContinuousPath.iSup_exitTimeTrunc : ⨆ n, exitTimeTrunc U n ω = exitTime U ω`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]









end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}









end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The expected exit time, untruncated

The expected exit time bound of `Trajectory/DynkinStopping.lean` is stated for the exit time
truncated at a deterministic horizon `K`, uniformly in `K`.  This file removes the truncation by
monotone convergence: under the same hypotheses (`L f ≤ -1` on the open set `U`, `f ≥ m`),

  `E_x τ_U ≤ f x - m`  (`IsFellerKernelSemigroup.lintegral_exitTime_le`),

as an `ℝ≥0∞`-valued integral of the `ℝ≥0∞`-valued exit time, so in particular the exit time from
`U` is almost surely finite from every starting point (`ae_exitTime_lt_top`).

It also records that the truncated exit time of `Path/ExitTime.lean` is the generic truncation
`StoppingTime.truncTime` of `Trajectory/StoppingLtTop.lean` applied to `exitTimeTop`
(`ContinuousPath.exitTimeTrunc_eq_truncTime`), and the monotone limit
`ContinuousPath.iSup_exitTimeTrunc : ⨆ n, exitTimeTrunc U n ω = exitTime U ω`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}



open MarkovProcess.SubMarkovKernelSemigroup in
omit [LocallyCompactSpace alpha] in

theorem MarkovProcess.SubMarkovKernelSemigroup.lintegral_exitTimeTrunc_eq (hP : P.IsConservative) (U : Set alpha) (hU : IsOpen U)
    (K : NNReal) (x : alpha) :
    ∫⁻ omega, ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ≥0∞)
        ∂(IsConservative.continuousProcess P hP x) =
      ENNReal.ofReal (∫ omega, ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x)) := by sorry
