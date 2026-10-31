-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_eval_stoppingTime_sub_eq_integral_integral_generator
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:33:40.525495+00:00
-- url     : https://prove2.me/theorems/f826ce45-b5f4-4e87-a586-e931217c8632
-- title:
--   MarkovProcess: integral_eval_stoppingTime_sub_eq_integral_integral_generator
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
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
# Dynkin's formula at a bounded stopping time, and the expected exit time

The Dynkin process of `f` in the generator domain is a martingale for the canonical filtration
under the continuous-path process `Q = continuousProcess P hP` (`martingale_dynkinProcess`), it is
bounded on bounded time intervals, and it is continuous in time along every path.  Optional
stopping (`MarkovProcess.integral_stoppedValue_eq_of_locallyBounded`) therefore applies at every
finite stopping time `T` bounded by a deterministic horizon, and gives **Dynkin's formula at a
bounded stopping time**:

  `E_x f(omega (T omega)) - f x = E_x ∫₀^{T omega} (L f)(omega s) ds`

(`integral_eval_stoppingTime_sub_eq_integral_integral_generator`, with the equivalent compact form
`integral_dynkinProcess_stoppingTime`).

The classical consequence is the **expected exit time bound**: if `L f ≤ -1` on an open set `U`
and `f` is bounded below by `m`, then the exit time from `U`, truncated at any horizon `K`, has
expectation at most `f x - m` from every starting point `x`
(`integral_exitTimeTrunc_le`).  The proof uses that strictly before the exit time the path is
still inside `U`, so the integrand of Dynkin's formula is at most `-1` there.

The truncation at `K` is what keeps the stopping time finite; the bound is uniform in `K`, and
`Trajectory/ExpectedExitTime.lean` removes the truncation by monotone convergence
(`lintegral_exitTime_le`, `ae_exitTime_lt_top`).

The progressive-measurability and optional-stopping statements below are the zero-discount
specializations of the corresponding results in `Trajectory/DiscountedDynkin.lean`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section ProgressiveMeasurability

variable [SecondCountableTopology alpha]





end ProgressiveMeasurability

section Stopping

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (hP : P.IsConservative)









end Stopping

section ExitTime

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (hP : P.IsConservative)









end ExitTime

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
# Dynkin's formula at a bounded stopping time, and the expected exit time

The Dynkin process of `f` in the generator domain is a martingale for the canonical filtration
under the continuous-path process `Q = continuousProcess P hP` (`martingale_dynkinProcess`), it is
bounded on bounded time intervals, and it is continuous in time along every path.  Optional
stopping (`MarkovProcess.integral_stoppedValue_eq_of_locallyBounded`) therefore applies at every
finite stopping time `T` bounded by a deterministic horizon, and gives **Dynkin's formula at a
bounded stopping time**:

  `E_x f(omega (T omega)) - f x = E_x ∫₀^{T omega} (L f)(omega s) ds`

(`integral_eval_stoppingTime_sub_eq_integral_integral_generator`, with the equivalent compact form
`integral_dynkinProcess_stoppingTime`).

The classical consequence is the **expected exit time bound**: if `L f ≤ -1` on an open set `U`
and `f` is bounded below by `m`, then the exit time from `U`, truncated at any horizon `K`, has
expectation at most `f x - m` from every starting point `x`
(`integral_exitTimeTrunc_le`).  The proof uses that strictly before the exit time the path is
still inside `U`, so the integrand of Dynkin's formula is at most `-1` there.

The truncation at `K` is what keeps the stopping time finite; the bound is uniform in `K`, and
`Trajectory/ExpectedExitTime.lean` removes the truncation by monotone convergence
(`lintegral_exitTime_le`, `ae_exitTime_lt_top`).

The progressive-measurability and optional-stopping statements below are the zero-discount
specializations of the corresponding results in `Trajectory/DiscountedDynkin.lean`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}



variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (hP : P.IsConservative)







open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega (T omega))
          ∂(IsConservative.continuousProcess P hP x) - (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..(T omega : ℝ),
          (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x) := by sorry
