-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_killedResolvent_le_of_perturbed_resolventFamily
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:33:54.992992+00:00
-- url     : https://prove2.me/theorems/2e5e10b9-786a-42e1-9090-c31006d4a270
-- title:
--   MarkovProcess: killedResolvent_le_of_perturbed_resolventFamily
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacRealResolvent_20f8c260
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
# Penalization domination for killed resolvents

A resolvent family preserving measurable bounded functions, satisfying the resolvent identity,
and solving the same bounded-potential perturbation equation as the real Feynman--Kac resolvent
dominates the killed resolvent of every open set on which the potential vanishes. The process-side
inputs are conservativity, the Feller property, and Kolmogorov regularity on a locally compact
Polish space.

Main result: `IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily`.
-/

open MeasureTheory Set
open scoped ENNReal

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
# Penalization domination for killed resolvents

A resolvent family preserving measurable bounded functions, satisfying the resolvent identity,
and solving the same bounded-potential perturbation equation as the real Feynman--Kac resolvent
dominates the killed resolvent of every open set on which the potential vanishes. The process-side
inputs are conservativity, the Feller property, and Kolmogorov regularity on a locally compact
Polish space.

Main result: `IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily`.
-/

open MeasureTheory Set
open scoped ENNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {q : alpha → ℝ} (hq : Measurable q)
    (hqU : ∀ y ∈ U, q y = 0) {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (Y : ℝ → (alpha → ℝ) → alpha → ℝ)
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hY_perturbation : ∀ {lam : ℝ}, C < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y lam f = P.kernelResolventReal lam f -
        P.kernelResolventReal lam (fun y ↦ q y * Y lam f y))
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam (fun y ↦ ENNReal.ofReal (f y)) x ≤
      ENNReal.ofReal (Y lam f x) := by sorry
