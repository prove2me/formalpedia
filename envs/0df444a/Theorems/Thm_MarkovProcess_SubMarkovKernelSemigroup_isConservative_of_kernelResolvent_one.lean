-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_isConservative_of_kernelResolvent_one
-- name    : MarkovProcess.SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:43.450974+00:00
-- url     : https://prove2.me/theorems/8bccbe96-622a-4608-ac98-84ef00e56dd8
-- title:
--   MarkovProcess: isConservative_of_kernelResolvent_one
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
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
# Conservativity from the resolvent of the constant observable

A sub-Markov kernel semigroup loses no mass as soon as its resolvent at one positive shift has
the full mass of the exponential weight,

  `lam * R_lam 1 = 1`   (`SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one`).

The transition mass is nonincreasing in time (`SubMarkovKernelSemigroup.measure_univ_le_of_le`),
because the Chapman--Kolmogorov law integrates a mass at most one against an earlier transition
law.  The hypothesis says that the Laplace transform of the transition mass equals the Laplace
transform of the constant observable one; both integrands are integrable and ordered, so they
agree at almost every time, and monotonicity in time upgrades this to every time.

The converse is immediate from the mass of the exponential weight
(`SubMarkovKernelSemigroup.IsConservative.kernelResolvent_one`,
`SubMarkovKernelSemigroup.IsConservative.ofReal_mul_kernelResolvent_one`), so the criterion is an
equivalence and not merely a sufficient condition.

No topology on the state space is used.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)











end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservativity from the resolvent of the constant observable

A sub-Markov kernel semigroup loses no mass as soon as its resolvent at one positive shift has
the full mass of the exponential weight,

  `lam * R_lam 1 = 1`   (`SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one`).

The transition mass is nonincreasing in time (`SubMarkovKernelSemigroup.measure_univ_le_of_le`),
because the Chapman--Kolmogorov law integrates a mass at most one against an earlier transition
law.  The hypothesis says that the Laplace transform of the transition mass equals the Laplace
transform of the constant observable one; both integrands are integrable and ordered, so they
agree at almost every time, and monotonicity in time upgrades this to every time.

The converse is immediate from the mass of the exponential weight
(`SubMarkovKernelSemigroup.IsConservative.kernelResolvent_one`,
`SubMarkovKernelSemigroup.IsConservative.ofReal_mul_kernelResolvent_one`), so the criterion is an
equivalence and not merely a sufficient condition.

No topology on the state space is used.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)





open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one {lam : ℝ} (hlam : 0 < lam)
    (hone : ∀ x, ENNReal.ofReal lam * P.kernelResolvent lam (fun _ ↦ 1) x = 1) :
    P.IsConservative := by sorry
