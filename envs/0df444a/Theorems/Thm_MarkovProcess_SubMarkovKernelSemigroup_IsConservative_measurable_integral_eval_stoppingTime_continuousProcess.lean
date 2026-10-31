-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_measurable_integral_eval_stoppingTime_continuousProcess
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.measurable_integral_eval_stoppingTime_continuousProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:30.036838+00:00
-- url     : https://prove2.me/theorems/1d080e46-7fcd-4d9a-93e1-5f37bd75c526
-- title:
--   MarkovProcess: measurable_integral_eval_stoppingTime_continuousProcess
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Tight
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
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal

namespace MarkovProcess


namespace SubMarkovKernelSemigroup

section BoundedContinuousTest

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [LocallyCompactSpace alpha]



end BoundedContinuousTest

noncomputable section Process

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]







end Measurability

section Continuity

variable [LocallyCompactSpace alpha]





end Continuity

end Process

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
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal






open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]





open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.measurable_integral_eval_stoppingTime_continuousProcess
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (G : alpha → E) (hG : StronglyMeasurable G) :
    Measurable fun x ↦ ∫ omega, G (omega (T omega)) ∂(continuousProcess P hP x) := by sorry
