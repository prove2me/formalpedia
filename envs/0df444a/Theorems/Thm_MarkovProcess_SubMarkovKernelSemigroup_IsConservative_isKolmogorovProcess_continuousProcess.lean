-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_isKolmogorovProcess_continuousProcess
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isKolmogorovProcess_continuousProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:47.786047+00:00
-- url     : https://prove2.me/theorems/3afe497a-2e41-4012-a83c-27c71a60c471
-- title:
--   MarkovProcess: isKolmogorovProcess_continuousProcess
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
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
import Mathlib.Topology.EMetricSpace.Basic
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
# The continuous-path process as a Kolmogorov process, and its uniform modulus

The intrinsic moment criterion `HasKolmogorovMoments p q M` is a statement about the transition
kernels.  This file transports it to the continuous-path process itself, at *all* nonnegative
real times and with the very same constants: the coordinate process of `continuousProcess P hP x`
is a Kolmogorov process with exponents `p`, `q` and constant `M`, for every starting point `x`.
Rational times come from the identification of the dense-time projection of the process with the
dense-time trajectory; irrational times follow by path continuity and Fatou's lemma, so no Feller
hypothesis and no local compactness are needed.

Combining this with the quantitative chaining estimate of `Continuity/PathModulus.lean` gives the
modulus statement that tightness on path space consumes: for a horizon `T`, an oscillation
tolerance `r` and a mass tolerance `eps` there is one scale `delta > 0` that works simultaneously
at every starting point.

Main results:

* `IsConservative.map_denseRestriction_continuousProcess`, the dense-time projection of the
  process;
* `IsConservative.isKolmogorovProcess_continuousProcess`, the moment bound at all real times;
* `IsConservative.exists_measure_compl_modulusSet_le`, the modulus estimate uniform in the
  starting point.

No tightness, weak continuity, or Hölder-path statement is proved here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)









end

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
# The continuous-path process as a Kolmogorov process, and its uniform modulus

The intrinsic moment criterion `HasKolmogorovMoments p q M` is a statement about the transition
kernels.  This file transports it to the continuous-path process itself, at *all* nonnegative
real times and with the very same constants: the coordinate process of `continuousProcess P hP x`
is a Kolmogorov process with exponents `p`, `q` and constant `M`, for every starting point `x`.
Rational times come from the identification of the dense-time projection of the process with the
dense-time trajectory; irrational times follow by path continuity and Fatou's lemma, so no Feller
hypothesis and no local compactness are needed.

Combining this with the quantitative chaining estimate of `Continuity/PathModulus.lean` gives the
modulus statement that tightness on path space consumes: for a horizon `T`, an oscillation
tolerance `r` and a mass tolerance `eps` there is one scale `delta > 0` that works simultaneously
at every starting point.

Main results:

* `IsConservative.map_denseRestriction_continuousProcess`, the dense-time projection of the
  process;
* `IsConservative.isKolmogorovProcess_continuousProcess`, the moment bound at all real times;
* `IsConservative.exists_measure_compl_modulusSet_le`, the modulus estimate uniform in the
  starting point.

No tightness, weak continuity, or Hölder-path statement is proved here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal




open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isKolmogorovProcess_continuousProcess
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (hK : P.KolmogorovRegular hP)
    (x : alpha) :
    IsKolmogorovProcess (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t)
      (continuousProcess P hP x) p q M := by sorry
