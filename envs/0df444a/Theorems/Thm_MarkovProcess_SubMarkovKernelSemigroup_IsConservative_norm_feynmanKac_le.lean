-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_norm_feynmanKac_le
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.norm_feynmanKac_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:24.389607+00:00
-- url     : https://prove2.me/theorems/d5e756d5-639b-40ef-a1eb-d192a9856fe0
-- title:
--   MarkovProcess: norm_feynmanKac_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Probability.Martingale.Basic
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
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]





variable [SecondCountableTopology alpha]























variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)






































end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]





variable [SecondCountableTopology alpha]























variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)































open MarkovProcess.SubMarkovKernelSemigroup in
omit [LocallyCompactSpace alpha] in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.norm_feynmanKac_le {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |IsConservative.feynmanKac P hP q t f x| ≤ D := by sorry
