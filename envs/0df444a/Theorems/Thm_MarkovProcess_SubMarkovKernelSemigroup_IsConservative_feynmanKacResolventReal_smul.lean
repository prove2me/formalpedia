-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_feynmanKacResolventReal_smul
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.feynmanKacResolventReal_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:36.549153+00:00
-- url     : https://prove2.me/theorems/d8738bfd-2a6f-4964-a4c2-f4ace5aa1c24
-- title:
--   MarkovProcess: feynmanKacResolventReal_smul
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacRealResolvent_20f8c260
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacResolvent_ed9736ae
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
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
import Mathlib.Probability.Martingale.OptionalStopping
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
# Real Feynman--Kac resolvents

This file defines the real Feynman--Kac resolvent on bounded measurable observables.  It proves
its uniform bound, linearity, the resolvent identity, and the bounded-potential perturbation
identity.

Main results: `IsConservative.feynmanKacResolventReal`,
`IsFellerKernelSemigroup.feynmanKacResolventReal_resolvent_identity`, and
`IsFellerKernelSemigroup.feynmanKacResolventReal_perturbation`.

Together with `perturbed_eq_of_resolventFamilies`, these identities characterize the
Feynman--Kac resolvent among bounded measurable resolvent families solving the same perturbation
equation at all sufficiently large shifts.  No model-specific realization is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

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
# Real Feynman--Kac resolvents

This file defines the real Feynman--Kac resolvent on bounded measurable observables.  It proves
its uniform bound, linearity, the resolvent identity, and the bounded-potential perturbation
identity.

Main results: `IsConservative.feynmanKacResolventReal`,
`IsFellerKernelSemigroup.feynmanKacResolventReal_resolvent_identity`, and
`IsFellerKernelSemigroup.feynmanKacResolventReal_perturbation`.

Together with `perturbed_eq_of_resolventFamilies`, these identities characterize the
Feynman--Kac resolvent among bounded measurable resolvent families solving the same perturbation
equation at all sufficiently large shifts.  No model-specific realization is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)









open MarkovProcess.SubMarkovKernelSemigroup in
omit [LocallyCompactSpace alpha] in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.feynmanKacResolventReal_smul (q : alpha → ℝ) (lam a : ℝ)
    (f : alpha → ℝ) :
    IsConservative.feynmanKacResolventReal P hP q lam (a • f) =
      a • IsConservative.feynmanKacResolventReal P hP q lam f := by sorry
