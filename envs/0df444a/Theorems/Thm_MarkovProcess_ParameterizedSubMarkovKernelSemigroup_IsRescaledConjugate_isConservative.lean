-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_IsRescaledConjugate_isConservative
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate.isConservative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:33:55.092857+00:00
-- url     : https://prove2.me/theorems/4f64f47d-1e07-4308-a712-fe540da68f8d
-- title:
--   MarkovProcess: isConservative
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
import Definitions.Def_MarkovProcess_V3H_Parameterized_Equivariance_252d78e3
import Definitions.Def_MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
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
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
# Equivariance of the parameterized continuous-path process

The equivariance theorem of `MarkovProcess/Trajectory/Equivariance.lean`, restated for a measurably
parameterized family of sub-Markov kernel semigroups.  Here the state map `e` and the time factor
`c` are accompanied by a measurable reparameterization `g` of the parameter space, and the
intertwining hypothesis is fibrewise:
`P' theta t x = ((P (g theta) (c * t)) (e.symm x)).map e`.

The conclusion is a single identity of kernels on `Theta × alpha`: the quenched continuous-path
process of `P'` is the quenched process of `P` pulled back along `(theta, x) ↦ (g theta, e.symm x)`
and pushed forward by `ContinuousPath.rescale e c`.  The proof is fibrewise, through the exact
fibre identity `IsConservative.continuousProcess_apply`.

Main results: `ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate` with its fibre form and
its transfers of conservativity and of the Kolmogorov moment criterion;
`IsConservative.continuousProcess_eq_map_rescale`, its pointwise form and its intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`; the covariance corollary
`IsConservative.continuousProcess_covariant` for a family that is its own rescaled conjugate, of
which stationarity and re-gauging covariance of a random environment (`g` the environment shift,
`e` the spatial translation, `c = 1`) are instances.

No scaling limit and no ergodic statement is asserted: the environment map `g`, the factor `c`
and both families are given in advance, and nothing is claimed about the law of the environment.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

section Measurability

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [TopologicalSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]





namespace IsRescaledConjugate

variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}





end IsRescaledConjugate

end Measurability

section Moments

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [PseudoEMetricSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]
variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}



end Moments

section ContinuousProcess

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha] [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
  (P' : ParameterizedSubMarkovKernelSemigroup Theta beta)
  (hP : P.IsConservative) (hP' : P'.IsConservative)









end ContinuousProcess

end

end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Equivariance of the parameterized continuous-path process

The equivariance theorem of `MarkovProcess/Trajectory/Equivariance.lean`, restated for a measurably
parameterized family of sub-Markov kernel semigroups.  Here the state map `e` and the time factor
`c` are accompanied by a measurable reparameterization `g` of the parameter space, and the
intertwining hypothesis is fibrewise:
`P' theta t x = ((P (g theta) (c * t)) (e.symm x)).map e`.

The conclusion is a single identity of kernels on `Theta × alpha`: the quenched continuous-path
process of `P'` is the quenched process of `P` pulled back along `(theta, x) ↦ (g theta, e.symm x)`
and pushed forward by `ContinuousPath.rescale e c`.  The proof is fibrewise, through the exact
fibre identity `IsConservative.continuousProcess_apply`.

Main results: `ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate` with its fibre form and
its transfers of conservativity and of the Kolmogorov moment criterion;
`IsConservative.continuousProcess_eq_map_rescale`, its pointwise form and its intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`; the covariance corollary
`IsConservative.continuousProcess_covariant` for a family that is its own rescaled conjugate, of
which stationarity and re-gauging covariance of a random environment (`g` the environment shift,
`e` the spatial translation, `c = 1`) are instances.

No scaling limit and no ergodic statement is asserted: the environment map `g`, the factor `c`
and both families are given in advance, and nothing is claimed about the law of the environment.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal




variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [TopologicalSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]






variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}



open MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate.isConservative (h : IsRescaledConjugate P P' g e c) (hP : P.IsConservative) :
    P'.IsConservative := by sorry
