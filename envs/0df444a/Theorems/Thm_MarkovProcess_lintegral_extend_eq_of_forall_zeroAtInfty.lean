-- Prove2me | Theorems.Thm_MarkovProcess_lintegral_extend_eq_of_forall_zeroAtInfty
-- name    : MarkovProcess.lintegral_extend_eq_of_forall_zeroAtInfty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:38.550057+00:00
-- url     : https://prove2.me/theorems/4779cd29-918b-4f20-af02-60d7c91c8571
-- title:
--   MarkovProcess: lintegral_extend_eq_of_forall_zeroAtInfty
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_GluingTransfer_c0e8ad8d
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
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
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
# From vanishing observables to measurable ones

An identity between a measure `nu` on a target space and a measure `mu` on a source space,
tested on observables which are supported in the range of a measurable embedding `i` and
extended by zero off it, propagates from continuous observables vanishing at infinity to all
nonnegative measurable observables
(`lintegral_extend_eq_of_forall_zeroAtInfty`).  The reason is that both sides are integrals
against finite Borel measures on the source space, and continuous observables with compact
support already separate finite Borel measures on a locally compact second-countable metric
space.

This is the bridge which upgrades an analytically supplied identity of resolvents, stated for
continuous observables vanishing at infinity, to the identity of the corresponding potential
measures.

No topology on the target space is used, and no relation between the two measures other than the
tested identity is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported

noncomputable section

namespace MarkovProcess

section Topological

variable {X : Type*} [TopologicalSpace X]





end Topological

section Measurable

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]





end Measurable

section Transfer

variable {X Y : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]



end Transfer

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# From vanishing observables to measurable ones

An identity between a measure `nu` on a target space and a measure `mu` on a source space,
tested on observables which are supported in the range of a measurable embedding `i` and
extended by zero off it, propagates from continuous observables vanishing at infinity to all
nonnegative measurable observables
(`lintegral_extend_eq_of_forall_zeroAtInfty`).  The reason is that both sides are integrals
against finite Borel measures on the source space, and continuous observables with compact
support already separate finite Borel measures on a locally compact second-countable metric
space.

This is the bridge which upgrades an analytically supplied identity of resolvents, stated for
continuous observables vanishing at infinity, to the identity of the corresponding potential
measures.

No topology on the target space is used, and no relation between the two measures other than the
tested identity is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported






variable {X Y : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]

open MarkovProcess in

theorem MarkovProcess.lintegral_extend_eq_of_forall_zeroAtInfty {i : X → Y} (hi : MeasurableEmbedding i)
    (nu : Measure Y) (mu : Measure X) [IsFiniteMeasure nu] [IsFiniteMeasure mu]
    (hc0 : ∀ f : C₀(X, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, Function.extend i (fun y ↦ ENNReal.ofReal (f y)) 0 z ∂nu =
        ∫⁻ y, ENNReal.ofReal (f y) ∂mu)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, Function.extend i g 0 z ∂nu = ∫⁻ y, g y ∂mu := by sorry
