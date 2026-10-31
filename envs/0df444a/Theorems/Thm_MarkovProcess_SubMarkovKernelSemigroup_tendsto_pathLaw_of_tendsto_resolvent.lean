-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_tendsto_pathLaw_of_tendsto_resolvent
-- name    : MarkovProcess.SubMarkovKernelSemigroup.tendsto_pathLaw_of_tendsto_resolvent
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:34:59.06219+00:00
-- url     : https://prove2.me/theorems/d0611ca4-1afc-488d-b51e-c4173a51d643
-- title:
--   MarkovProcess: tendsto_pathLaw_of_tendsto_resolvent
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeConvergence_4d25bc20
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_WeakContinuity_59a9cfa0
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
# Weak convergence of Feller processes on path space

`Trajectory/Convergence.lean` proves that strong convergence of the `C₀` semigroups makes the
finite-dimensional distributions of the continuous-path processes converge.  This file upgrades
that to convergence of the whole path laws, provided the approximating semigroups and the limit
semigroup satisfy **one common** intrinsic Kolmogorov moment bound `HasKolmogorovMoments p q M`.

The common moment bound is what makes the family of path laws at a fixed starting point tight:
the scale in the modulus estimate of `Continuity/PathModulus.lean` depends only on the exponents,
the constant and the tolerances, never on the semigroup, so one compact set of paths carries all
but a prescribed mass of every law of the family at once.  On that compact set Stone--Weierstrass
replaces a bounded continuous functional of the path by a bounded cylinder functional
(`Trajectory/CylinderAlgebra.lean`), whose expectations converge by the finite-dimensional
theorem.  Three epsilons finish the argument; no compactness theorem for measures is used.

Main results:

* `isTightMeasureSet_insert_continuousProcess` and
  `exists_isCompact_measure_compl_le_insert`, tightness of the family of path laws at a fixed
  starting point;
* `tendsto_integral_continuousProcess`, convergence of the expectation of every bounded
  continuous functional of the path;
* `tendsto_pathLaw`, the same statement read in the space of probability measures on path space
  with its topology of convergence in distribution, and
  `tendsto_pathLaw_of_tendsto_resolvent`, its form starting from the resolvents.

The state space is assumed proper, as in `Trajectory/PathTightness.lean`, and the moment bound is
assumed with the same exponents and constant for every member of the family; nothing is asserted
when the constants are allowed to vary, nor for a family whose limit is not itself the process of
a Feller semigroup.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal ZeroAtInfty

namespace MarkovProcess


namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}











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
# Weak convergence of Feller processes on path space

`Trajectory/Convergence.lean` proves that strong convergence of the `C₀` semigroups makes the
finite-dimensional distributions of the continuous-path processes converge.  This file upgrades
that to convergence of the whole path laws, provided the approximating semigroups and the limit
semigroup satisfy **one common** intrinsic Kolmogorov moment bound `HasKolmogorovMoments p q M`.

The common moment bound is what makes the family of path laws at a fixed starting point tight:
the scale in the modulus estimate of `Continuity/PathModulus.lean` depends only on the exponents,
the constant and the tolerances, never on the semigroup, so one compact set of paths carries all
but a prescribed mass of every law of the family at once.  On that compact set Stone--Weierstrass
replaces a bounded continuous functional of the path by a bounded cylinder functional
(`Trajectory/CylinderAlgebra.lean`), whose expectations converge by the finite-dimensional
theorem.  Three epsilons finish the argument; no compactness theorem for measures is used.

Main results:

* `isTightMeasureSet_insert_continuousProcess` and
  `exists_isCompact_measure_compl_le_insert`, tightness of the family of path laws at a fixed
  starting point;
* `tendsto_integral_continuousProcess`, convergence of the expectation of every bounded
  continuous functional of the path;
* `tendsto_pathLaw`, the same statement read in the space of probability measures on path space
  with its topology of convergence in distribution, and
  `tendsto_pathLaw_of_tendsto_resolvent`, its form starting from the resolvents.

The state space is assumed proper, as in `Trajectory/PathTightness.lean`, and the moment bound is
assumed with the same exponents and constant for every member of the family; nothing is asserted
when the constants are allowed to vary, nor for a family whose limit is not itself the process of
a Feller semigroup.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal ZeroAtInfty





open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}









open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.tendsto_pathLaw_of_tendsto_resolvent
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    {mu : Semigroup.PositiveShift}
    (hres : ∀ f : C₀(alpha, ℝ), Tendsto (fun i ↦ (hP i).c0Semigroup.resolvent mu f) l
      (nhds (hQ.c0Semigroup.resolvent mu f))) (x : alpha) :
    Tendsto (fun i ↦ IsConservative.pathLaw (P i) (hPc i) x) l
      (nhds (IsConservative.pathLaw Q hQc x)) := by sorry
