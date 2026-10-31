-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_IsConservative_integral_annealedProcess
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.integral_annealedProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:33:44.936679+00:00
-- url     : https://prove2.me/theorems/821dbd65-4a32-4ca3-b6ab-cb319948b7cd
-- title:
--   MarkovProcess: integral_annealedProcess
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Parameterized_Annealed_005d5fdd
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
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
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The annealed law of a parameterized continuous-path process

For a measurably parameterized family of semigroups with quenched continuous-path process
`Q : Kernel (Theta × alpha) (ContinuousPath alpha)` and a law `mu` on the parameter space, the
**annealed process** is the kernel from the starting state to path space obtained by averaging
the parameter,

  `annealedProcess P hP mu x = ∫ Q (theta, x) mu(dtheta)`

(`annealedProcess_apply`, as a `Measure.bind`).  This file records the facts a consumer needs to
pass between quenched and annealed expectations: the annealed process is a Markov kernel when
`mu` is a probability law; annealed expectations are the `mu`-averages of quenched expectations
(`lintegral_annealedProcess`, `integral_annealedProcess`); and the annealed finite-dimensional
distributions and starting law are the averages of the quenched ones
(`annealedProcess_map_finiteEvaluation_apply`, `annealedProcess_map_eval_zero`).

The annealed process is in general not Markov in the probabilistic sense (the averaged law does
not have the Markov property); nothing of that kind is claimed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
variable (mu : Measure Theta) [SFinite mu]













variable [LocallyCompactSpace alpha]





end MarkovProcess.ParameterizedSubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The annealed law of a parameterized continuous-path process

For a measurably parameterized family of semigroups with quenched continuous-path process
`Q : Kernel (Theta × alpha) (ContinuousPath alpha)` and a law `mu` on the parameter space, the
**annealed process** is the kernel from the starting state to path space obtained by averaging
the parameter,

  `annealedProcess P hP mu x = ∫ Q (theta, x) mu(dtheta)`

(`annealedProcess_apply`, as a `Measure.bind`).  This file records the facts a consumer needs to
pass between quenched and annealed expectations: the annealed process is a Markov kernel when
`mu` is a probability law; annealed expectations are the `mu`-averages of quenched expectations
(`lintegral_annealedProcess`, `integral_annealedProcess`); and the annealed finite-dimensional
distributions and starting law are the averages of the quenched ones
(`annealedProcess_map_finiteEvaluation_apply`, `annealedProcess_map_eval_zero`).

The annealed process is in general not Markov in the probabilistic sense (the averaged law does
not have the Markov property); nothing of that kind is claimed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal


variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
variable (mu : Measure Theta) [SFinite mu]











open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.integral_annealedProcess [IsProbabilityMeasure mu] (x : alpha)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F) (C : ℝ)
    (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ∫ omega, F omega ∂(IsConservative.annealedProcess P hP mu x) =
      ∫ theta, ∫ omega, F omega ∂(IsConservative.continuousProcess P hP (theta, x)) ∂mu := by sorry
