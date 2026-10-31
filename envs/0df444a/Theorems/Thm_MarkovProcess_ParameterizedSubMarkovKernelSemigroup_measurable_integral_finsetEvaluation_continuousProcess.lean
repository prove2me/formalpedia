-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_measurable_integral_finsetEvaluation_continuousProcess
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.measurable_integral_finsetEvaluation_continuousProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:33:59.119323+00:00
-- url     : https://prove2.me/theorems/81d8f7e2-ab5a-46fe-a841-b5f173acaa8c
-- title:
--   MarkovProcess: measurable_integral_finsetEvaluation_continuousProcess
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_MeasureFiniteRestrictionIdentification_470add42
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeTrajectory_d8dd1c30
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
# The continuous-path process of a measurably parameterized semigroup

For a jointly measurable family of sub-Markov kernel semigroups indexed by a measurable parameter
space `Theta`, this file constructs the quenched continuous-path process as a single kernel
`Kernel (Theta × alpha) (ContinuousPath alpha)`: joint measurability in the parameter and the
starting state is carried by the kernel structure, not proved parameter by parameter afterwards.

The construction transports the jointly measurable dense-time trajectory
`parameterizedDenseTimeTrajectory` through the same measurable continuous-extension map that the
unparameterized `continuousProcess` uses, with the same fallback path.  The central result is the
fibre identity: at every parameter and every starting point the parameterized process is
*literally* the unparameterized process of that parameter's semigroup, with no null set and no
regularity hypothesis.  It rests on the corresponding dense-time fibre identity, which is proved
here from the finite enumeration-prefix marginals of the two trajectory kernels.

Fibrewise conservativity, Kolmogorov regularity and Kolmogorov moment bounds are named as
predicates on the parameterized family, so that consumers state hypotheses once.

No Markov, strong Markov, Feller, equivariance, annealed or killed statement is proved here; each
of those is a separate transport through the fibre identity.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

section Conservativity

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



end Conservativity

section Moments

variable {Theta alpha : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha]



end Moments

section DenseTimeFibre

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]





end DenseTimeFibre

section ContinuousProcess

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

















section QuenchedExpectations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]





end QuenchedExpectations

end ContinuousProcess

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path process of a measurably parameterized semigroup

For a jointly measurable family of sub-Markov kernel semigroups indexed by a measurable parameter
space `Theta`, this file constructs the quenched continuous-path process as a single kernel
`Kernel (Theta × alpha) (ContinuousPath alpha)`: joint measurability in the parameter and the
starting state is carried by the kernel structure, not proved parameter by parameter afterwards.

The construction transports the jointly measurable dense-time trajectory
`parameterizedDenseTimeTrajectory` through the same measurable continuous-extension map that the
unparameterized `continuousProcess` uses, with the same fallback path.  The central result is the
fibre identity: at every parameter and every starting point the parameterized process is
*literally* the unparameterized process of that parameter's semigroup, with no null set and no
regularity hypothesis.  It rests on the corresponding dense-time fibre identity, which is proved
here from the finite enumeration-prefix marginals of the two trajectory kernels.

Fibrewise conservativity, Kolmogorov regularity and Kolmogorov moment bounds are named as
predicates on the parameterized family, so that consumers state hypotheses once.

No Markov, strong Markov, Feller, equivariance, annealed or killed statement is proved here; each
of those is a separate transport through the fibre identity.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal







variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)


















variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]



open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.measurable_integral_finsetEvaluation_continuousProcess (I : Finset NNReal)
    (f : (I → alpha) → E) (hf : StronglyMeasurable f) :
    Measurable fun p : Theta × alpha ↦
      ∫ eta, f (ContinuousPath.finsetEvaluation I eta)
        ∂IsConservative.continuousProcess P hP p := by sorry
