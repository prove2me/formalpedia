-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_stoppedLaw_map_fst
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.stoppedLaw_map_fst
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:39.666543+00:00
-- url     : https://prove2.me/theorems/00dfd955-d97e-4a83-abe9-ab84dc5f09d9
-- title:
--   MarkovProcess: stoppedLaw_map_fst
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
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
# Stopped laws and exit distributions

For the continuous-path process `Q` of a conservative semigroup, this file packages as kernels the
laws that the strong Markov property and the boundary value problems of a domain consume:

* `stoppedLaw T hT : Kernel alpha (NNReal × alpha)`, the joint law of a finite stopping time and
  the position at that time, with its two marginals;
* `exitLawTrunc U hU K : Kernel alpha alpha`, the law of the position at the exit time of an open
  set `U` truncated at the horizon `K`; from a starting point in `U` it lives on the closure of `U`
  (`exitLawTrunc_apply_compl_closure`);
* `exitLaw U hU : Kernel alpha alpha`, the exit distribution (harmonic measure): the law of the
  position at the exit time on the event that the path leaves `U`; its total mass is the exit
  probability, and from a starting point in `U` it lives on the frontier of `U`
  (`exitLaw_apply_compl_frontier`).

The harmonic representation of `Trajectory/HarmonicRepresentation.lean` reads, in these terms,
`∫ f d(exitLawTrunc U hU K x) = f x` whenever `L f = 0` on `U`
(`integral_exitLawTrunc_eq_of_generator_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



variable [MeasurableSpace alpha] [BorelSpace alpha]







end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)

section StoppedLaw

variable (T : ContinuousPath alpha → NNReal)
  (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
    (fun omega ↦ (T omega : WithTop NNReal)))











end StoppedLaw

section ExitLaw

variable (U : Set alpha) (hU : IsOpen U)



















variable [LocallyCompactSpace alpha]



end ExitLaw

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
# Stopped laws and exit distributions

For the continuous-path process `Q` of a conservative semigroup, this file packages as kernels the
laws that the strong Markov property and the boundary value problems of a domain consume:

* `stoppedLaw T hT : Kernel alpha (NNReal × alpha)`, the joint law of a finite stopping time and
  the position at that time, with its two marginals;
* `exitLawTrunc U hU K : Kernel alpha alpha`, the law of the position at the exit time of an open
  set `U` truncated at the horizon `K`; from a starting point in `U` it lives on the closure of `U`
  (`exitLawTrunc_apply_compl_closure`);
* `exitLaw U hU : Kernel alpha alpha`, the exit distribution (harmonic measure): the law of the
  position at the exit time on the event that the path leaves `U`; its total mass is the exit
  probability, and from a starting point in `U` it lives on the frontier of `U`
  (`exitLaw_apply_compl_frontier`).

The harmonic representation of `Trajectory/HarmonicRepresentation.lean` reads, in these terms,
`∫ f d(exitLawTrunc U hU K x) = f x` whenever `L f = 0` on `U`
(`integral_exitLawTrunc_eq_of_generator_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)


variable (T : ContinuousPath alpha → NNReal)
  (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
    (fun omega ↦ (T omega : WithTop NNReal)))







open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.stoppedLaw_map_fst :
    (IsConservative.stoppedLaw hP T hT).map Prod.fst =
      (IsConservative.continuousProcess P hP).map T := by sorry
