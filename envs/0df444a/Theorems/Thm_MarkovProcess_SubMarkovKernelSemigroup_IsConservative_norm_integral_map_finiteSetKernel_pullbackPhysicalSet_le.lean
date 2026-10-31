-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:57.341264+00:00
-- url     : https://prove2.me/theorems/601e5080-e5dd-4834-af68-9740cd682ef3
-- title:
--   MarkovProcess: norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalCompactTestTransport_e18ed42b
import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact-test bounds for finite dense-time laws

Compact-test integrals against a physically indexed finite-set kernel, reindexed by dense-time
labels, are continuous in the starting point. Conservativity also gives a uniform norm bound by
the `C₀` norm of the test. Both statements include the empty coordinate set.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Continuity

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



end Continuity

section Bound

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]



end Bound

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact-test bounds for finite dense-time laws

Compact-test integrals against a physically indexed finite-set kernel, reindexed by dense-time
labels, are continuous in the starting point. Conservativity also gives a uniform norm bound by
the `C₀` norm of the test. Both statements include the empty coordinate set.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported ZeroAtInfty




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) (y : alpha) :
    ‖∫ z, f z ∂(finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J) y‖ ≤
      ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖ := by sorry
