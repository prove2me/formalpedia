-- Prove2me | Theorems.Thm_MarkovProcess_isFiniteMeasure_laplaceWeight
-- name    : MarkovProcess.isFiniteMeasure_laplaceWeight
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:19.422219+00:00
-- url     : https://prove2.me/theorems/19e917c9-927b-4889-ad0b-dc196a09f9e6
-- title:
--   MarkovProcess: isFiniteMeasure_laplaceWeight
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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
# Potential measures

The resolvent of a transition family at a shift `lam` integrates an observable against the
exponentially weighted time average of its transition kernels.  This file realises that average
as a genuine measure, the `lam`-potential measure

  `laplacePotential lam mu = ∫_0^∞ e^{-lam t} (mu t) dt`,

so that both the kernel resolvent of a sub-Markov kernel semigroup and the killed resolvent of an
open set are integrals against a measure on the state space:
`SubMarkovKernelSemigroup.lintegral_resolventPotential` and
`IsConservative.lintegral_killedPotential`.  Potential measures of sub-Markov families are finite
at every positive shift, with total mass at most `1 / lam`.

Two consequences of the measure form are proved here: the killed resolvent is monotone in the
open set and in the observable (`IsConservative.killedResolvent_mono`), and the kernel resolvent
is measurable in the starting point and continuous along monotone limits of observables
(`SubMarkovKernelSemigroup.measurable_kernelResolvent`,
`SubMarkovKernelSemigroup.kernelResolvent_iSup`).  The kernel resolvent is also additive and
homogeneous on measurable observables (`SubMarkovKernelSemigroup.kernelResolvent_add`,
`SubMarkovKernelSemigroup.kernelResolvent_const_mul`).

No resolvent identity and no topology on the state space are used here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess











variable {alpha : Type*} [MeasurableSpace alpha]









namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup alpha)























section Killed

variable [MetricSpace alpha] [CompleteSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)











end Killed

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Potential measures

The resolvent of a transition family at a shift `lam` integrates an observable against the
exponentially weighted time average of its transition kernels.  This file realises that average
as a genuine measure, the `lam`-potential measure

  `laplacePotential lam mu = ∫_0^∞ e^{-lam t} (mu t) dt`,

so that both the kernel resolvent of a sub-Markov kernel semigroup and the killed resolvent of an
open set are integrals against a measure on the state space:
`SubMarkovKernelSemigroup.lintegral_resolventPotential` and
`IsConservative.lintegral_killedPotential`.  Potential measures of sub-Markov families are finite
at every positive shift, with total mass at most `1 / lam`.

Two consequences of the measure form are proved here: the killed resolvent is monotone in the
open set and in the observable (`IsConservative.killedResolvent_mono`), and the kernel resolvent
is measurable in the starting point and continuous along monotone limits of observables
(`SubMarkovKernelSemigroup.measurable_kernelResolvent`,
`SubMarkovKernelSemigroup.kernelResolvent_iSup`).  The kernel resolvent is also additive and
homogeneous on measurable observables (`SubMarkovKernelSemigroup.kernelResolvent_add`,
`SubMarkovKernelSemigroup.kernelResolvent_const_mul`).

No resolvent identity and no topology on the state space are used here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal











open MarkovProcess in

theorem MarkovProcess.isFiniteMeasure_laplaceWeight {lam : ℝ} (hlam : 0 < lam) :
    IsFiniteMeasure (laplaceWeight lam) := by sorry
