-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_isLambdaExcessive_of_c0Semigroup_apply_le_exp_mul
-- name    : MarkovProcess.SubMarkovKernelSemigroup.isLambdaExcessive_of_c0Semigroup_apply_le_exp_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:59.183891+00:00
-- url     : https://prove2.me/theorems/37a610be-aa7f-47be-8465-ed0a63f721a3
-- title:
--   MarkovProcess: isLambdaExcessive_of_c0Semigroup_apply_le_exp_mul
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExcessiveStopping_8ea33a1f
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
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
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Excessive functions and stopping

This file turns the semigroup definition of an exponentially excessive `C₀` function into a
supermartingale along the canonical continuous process.  Continuous-time optional stopping then
gives the corresponding inequality at bounded stopping times and, by Fatou's lemma, at the finite
exit time from an open set.

The exit inequality is the lower-bound half paired with
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.  No model-specific
assumptions enter here.

Main results: `IsFellerKernelSemigroup.resolvent_isLambdaExcessive`,
`IsLambdaExcessive.supermartingale_discountedValueProcess`,
`IsLambdaExcessive.integral_discountedValueProcess_stoppingTime_le`, and
`IsLambdaExcessive.lintegral_discountedValue_exitTime_le`.

No converse characterization of excessive functions is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

section Supermedian

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}





end Supermedian

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}























end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Excessive functions and stopping

This file turns the semigroup definition of an exponentially excessive `C₀` function into a
supermartingale along the canonical continuous process.  Continuous-time optional stopping then
gives the corresponding inequality at bounded stopping times and, by Fatou's lemma, at the finite
exit time from an open set.

The exit inequality is the lower-bound half paired with
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.  No model-specific
assumptions enter here.

Main results: `IsFellerKernelSemigroup.resolvent_isLambdaExcessive`,
`IsLambdaExcessive.supermartingale_discountedValueProcess`,
`IsLambdaExcessive.integral_discountedValueProcess_stoppingTime_le`, and
`IsLambdaExcessive.lintegral_discountedValue_exitTime_le`.

No converse characterization of excessive functions is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}



open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.isLambdaExcessive_of_c0Semigroup_apply_le_exp_mul
    (lam : ℝ) (v : C₀(alpha, ℝ))
    (hv : ∀ x, 0 ≤ v x)
    (hcomp : ∀ (t : NNReal) (x : alpha),
      kernelIntegral (P t) v x ≤ Real.exp (lam * (t : ℝ)) * v x) :
    P.IsLambdaExcessive lam v := by sorry
