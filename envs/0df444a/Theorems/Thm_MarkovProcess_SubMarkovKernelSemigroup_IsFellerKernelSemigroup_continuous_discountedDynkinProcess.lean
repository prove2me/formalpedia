-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuous_discountedDynkinProcess
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuous_discountedDynkinProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:07.27247+00:00
-- url     : https://prove2.me/theorems/47e2ffd7-e312-48a1-a4e0-26c0ae06b78a
-- title:
--   MarkovProcess: continuous_discountedDynkinProcess
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
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
# The discounted Dynkin formula

For the continuous-path process of a conservative Feller semigroup, this file proves that the
Dynkin process with exponential discount is a martingale and applies optional stopping at an exit
time truncated by a deterministic horizon.  At zero discount it agrees with the Dynkin process
of `Trajectory/DynkinMartingale.lean`.

Main results: `IsFellerKernelSemigroup.discountedDynkinProcess`,
`discountedDynkinProcess_apply`, `discountedDynkinProcess_zero`,
`norm_discountedDynkinProcess_le`, `continuous_discountedDynkinProcess`,
`stronglyMeasurable_integral_discountedGenerator`,
`stronglyMeasurable_discountedDynkinProcess_canonicalFiltration`,
`stronglyMeasurable_discountedDynkinProcess`, `adapted_discountedDynkinProcess`,
`integrable_discountedDynkinProcess`, `integral_discountedDynkinProcess`,
`discountedDynkinProcess_eq_add_shift`, `martingale_discountedDynkinProcess`,
`progMeasurable_discountedDynkinProcess`, `measurable_discountedDynkinProcess_stoppingTime`,
`integral_discountedDynkinProcess_stoppingTime`, and
`integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral`.

No assertion is made at an unbounded stopping time or about passage to an infinite horizon.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section ProcessDefinition













end ProcessDefinition

section Adapted

variable [SecondCountableTopology alpha]











end Adapted

section Expectation

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)





end Expectation

section Decomposition



end Decomposition

section Martingale

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)



end Martingale

section OptionalStopping

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)









end OptionalStopping

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
# The discounted Dynkin formula

For the continuous-path process of a conservative Feller semigroup, this file proves that the
Dynkin process with exponential discount is a martingale and applies optional stopping at an exit
time truncated by a deterministic horizon.  At zero discount it agrees with the Dynkin process
of `Trajectory/DynkinMartingale.lean`.

Main results: `IsFellerKernelSemigroup.discountedDynkinProcess`,
`discountedDynkinProcess_apply`, `discountedDynkinProcess_zero`,
`norm_discountedDynkinProcess_le`, `continuous_discountedDynkinProcess`,
`stronglyMeasurable_integral_discountedGenerator`,
`stronglyMeasurable_discountedDynkinProcess_canonicalFiltration`,
`stronglyMeasurable_discountedDynkinProcess`, `adapted_discountedDynkinProcess`,
`integrable_discountedDynkinProcess`, `integral_discountedDynkinProcess`,
`discountedDynkinProcess_eq_add_shift`, `martingale_discountedDynkinProcess`,
`progMeasurable_discountedDynkinProcess`, `measurable_discountedDynkinProcess_stoppingTime`,
`integral_discountedDynkinProcess_stoppingTime`, and
`integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral`.

No assertion is made at an unbounded stopping time or about passage to an infinite horizon.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}












open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuous_discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (omega : ContinuousPath alpha) :
    Continuous fun t : NNReal ↦ hFeller.discountedDynkinProcess f lam t omega := by sorry
