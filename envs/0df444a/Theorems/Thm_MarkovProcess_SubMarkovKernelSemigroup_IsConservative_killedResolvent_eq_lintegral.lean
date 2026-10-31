-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedResolvent_eq_lintegral
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedResolvent_eq_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:15.561314+00:00
-- url     : https://prove2.me/theorems/0cb6e472-1c40-4d54-b7ee-fdcd9376d893
-- title:
--   MarkovProcess: killedResolvent_eq_lintegral
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Killed_Kernel_adff808d
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
# The killed resolvent

The resolvent of the process killed at the exit of an open set `U`, at the shift `λ > 0`, is the
Laplace transform of the killed kernels,

  `killedResolvent λ f x = ∫ t in (0, ∞), e^{-λ t} (∫ f d(killedKernel t x)) dt`,

and this file proves the path-space formula

  `killedResolvent λ f x = E_x ∫_0^{τ_U} e^{-λ t} f(ω_t) dt`

(`killedResolvent_eq_lintegral`), for nonnegative extended measurable `f`; the integral over time
runs up to the exit time, where the survival indicator vanishes. The statement is an identity of
`ℝ≥0∞`-valued integrals, proved by Tonelli's theorem, so it carries no integrability hypothesis;
a consumer working with real-valued bounded `f` splits it into its positive and negative parts.

This is the probabilistic side of the Dirichlet resolvent `(λ − L)⁻¹` on `U` with zero boundary
values: the identification with the analytic resolvent of a given operator is the consumer's
statement about that operator.  One order fact is recorded alongside: the killed resolvent is
antitone in the shift (`IsConservative.killedResolvent_antitone`), because a larger shift
discounts the future more.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)









end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The killed resolvent

The resolvent of the process killed at the exit of an open set `U`, at the shift `λ > 0`, is the
Laplace transform of the killed kernels,

  `killedResolvent λ f x = ∫ t in (0, ∞), e^{-λ t} (∫ f d(killedKernel t x)) dt`,

and this file proves the path-space formula

  `killedResolvent λ f x = E_x ∫_0^{τ_U} e^{-λ t} f(ω_t) dt`

(`killedResolvent_eq_lintegral`), for nonnegative extended measurable `f`; the integral over time
runs up to the exit time, where the survival indicator vanishes. The statement is an identity of
`ℝ≥0∞`-valued integrals, proved by Tonelli's theorem, so it carries no integrability hypothesis;
a consumer working with real-valued bounded `f` splits it into its positive and negative parts.

This is the probabilistic side of the Dirichlet resolvent `(λ − L)⁻¹` on `U` with zero boundary
values: the identification with the analytic resolvent of a given operator is the consumer's
statement about that operator.  One order fact is recorded alongside: the killed resolvent is
antitone in the shift (`IsConservative.killedResolvent_antitone`), because a larger shift
discounts the future more.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal


variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)





open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedResolvent_eq_lintegral (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x =
      ∫⁻ omega, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
            (fun t ↦ f (omega (Real.toNNReal t))) t)
        ∂(IsConservative.continuousProcess P hP x) := by sorry
