-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuous_integral_continuousProcess
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuous_integral_continuousProcess
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:33:13.653776+00:00
-- url     : https://prove2.me/theorems/4841d050-e2cd-4274-bbb0-722d4722b5ba
-- title:
--   MarkovProcess: continuous_integral_continuousProcess
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Continuity_PathTightness_ad16da33
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
import Definitions.Def_MarkovProcess_V3H_Trajectory_CylinderAlgebra_cdb093fb
import Definitions.Def_MarkovProcess_V3H_Trajectory_WeakContinuity_59a9cfa0
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
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
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
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Weak continuity of the path law in the starting point

`Trajectory/StartingPointContinuity.lean` proves that cylinder expectations of the
continuous-path process depend continuously on the starting point.  This file upgrades that to
*every* bounded continuous functional of the path, which is weak continuity of the path law
itself.

The route needs no compactness theorem for measures.  Fix a starting point `x0` and a compact
neighbourhood `K0` of it.  Tightness (`Trajectory/PathTightness.lean`) produces one compact set of
paths carrying all but `eta` of the mass from every starting point of `K0`.  On that compact set
Stone--Weierstrass replaces the given functional by a bounded cylinder functional, with a norm
bound that makes the discarded mass cheap (`Trajectory/CylinderAlgebra.lean`), and the cylinder
functional is already known to have continuous expectations.  Three epsilons and a triangle
inequality finish the argument.

Main results:

* `IsFellerKernelSemigroup.continuous_integral_boundedCylinder`, continuity for cylinder
  functionals;
* `IsFellerKernelSemigroup.continuous_integral_continuousProcess`, continuity for every bounded
  continuous functional of the path;
* `IsConservative.pathLaw` and `IsFellerKernelSemigroup.continuous_pathLaw`, the same statement
  read as continuity into the space of probability measures on path space with its topology of
  convergence in distribution.

Nothing here asserts relative compactness of a family of laws, and no convergence of a sequence
of semigroups is treated.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace MarkovProcess

section TruncationError

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]



end TruncationError

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]

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
# Weak continuity of the path law in the starting point

`Trajectory/StartingPointContinuity.lean` proves that cylinder expectations of the
continuous-path process depend continuously on the starting point.  This file upgrades that to
*every* bounded continuous functional of the path, which is weak continuity of the path law
itself.

The route needs no compactness theorem for measures.  Fix a starting point `x0` and a compact
neighbourhood `K0` of it.  Tightness (`Trajectory/PathTightness.lean`) produces one compact set of
paths carrying all but `eta` of the mass from every starting point of `K0`.  On that compact set
Stone--Weierstrass replaces the given functional by a bounded cylinder functional, with a norm
bound that makes the discarded mass cheap (`Trajectory/CylinderAlgebra.lean`), and the cylinder
functional is already known to have continuous expectations.  Three epsilons and a triangle
inequality finish the argument.

Main results:

* `IsFellerKernelSemigroup.continuous_integral_boundedCylinder`, continuity for cylinder
  functionals;
* `IsFellerKernelSemigroup.continuous_integral_continuousProcess`, continuity for every bounded
  continuous functional of the path;
* `IsConservative.pathLaw` and `IsFellerKernelSemigroup.continuous_pathLaw`, the same statement
  read as continuity into the space of probability measures on path space with its topology of
  convergence in distribution.

Nothing here asserts relative compactness of a family of laws, and no convergence of a sequence
of semigroups is treated.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal





open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuous_integral_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) (F : ContinuousPath alpha →ᵇ ℝ) :
    Continuous fun x ↦ ∫ omega, F omega ∂(continuousProcess P hP x) := by sorry
