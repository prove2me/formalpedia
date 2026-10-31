-- Prove2me | Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_kernelResolvent_le_of_partProcess
-- name    : MarkovProcess.PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:34:13.267992+00:00
-- url     : https://prove2.me/theorems/345ab11b-b5b1-4be8-bb24-e17022a69da2
-- title:
--   MarkovProcess: kernelResolvent_le_of_partProcess
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingTransfer_c0e8ad8d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
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
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Comparing two local resolvents through the part-process identity

Two positive `C₀`-contractive resolvents on nested locally compact state spaces are compared here
through the process of the larger one.  The data are an open embedding `iota : X₀ → X₁`, the
regularity data (`PositiveC0ContractiveResolvent.OnePointRegular`) which the continuous-path
process of the compactification of `X₁` is formed from, and the part-process identity: the
resolvent of the process of `X₁` killed at the exit from the image of `X₀` is the resolvent
supplied on `X₀`.

The conclusion (`PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess`) is that the
kernel resolvent of the smaller space is dominated by the kernel resolvent of the larger one: a
path leaves the smaller domain no later, so it accumulates less.  The identity is supplied for
nonnegative continuous observables vanishing at infinity, which is the form an analytic
construction produces, and is upgraded to all nonnegative measurable observables through the
potential measures.

The regularity data are an explicit hypothesis: positivity, contractivity and the resolvent
identity do not by themselves give the compactified semigroup a continuous-path process.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]



namespace OnePointRegular

variable {R : PositiveC0ContractiveResolvent X}













end OnePointRegular



section Embedding

variable {X₀ X₁ : Type*}











end Embedding

section EmbeddingTopology

variable {X₀ X₁ : Type*} [TopologicalSpace X₀] [TopologicalSpace X₁]





end EmbeddingTopology

section Comparison

variable {X₀ X₁ : Type*}
  [MetricSpace X₀] [LocallyCompactSpace X₀] [SecondCountableTopology X₀]
  [MeasurableSpace X₀] [BorelSpace X₀]
  [MetricSpace X₁] [LocallyCompactSpace X₁] [SecondCountableTopology X₁]
  [MeasurableSpace X₁] [BorelSpace X₁]





end Comparison

end MarkovProcess.PositiveC0ContractiveResolvent


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Comparing two local resolvents through the part-process identity

Two positive `C₀`-contractive resolvents on nested locally compact state spaces are compared here
through the process of the larger one.  The data are an open embedding `iota : X₀ → X₁`, the
regularity data (`PositiveC0ContractiveResolvent.OnePointRegular`) which the continuous-path
process of the compactification of `X₁` is formed from, and the part-process identity: the
resolvent of the process of `X₁` killed at the exit from the image of `X₀` is the resolvent
supplied on `X₀`.

The conclusion (`PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess`) is that the
kernel resolvent of the smaller space is dominated by the kernel resolvent of the larger one: a
path leaves the smaller domain no later, so it accumulates less.  The identity is supplied for
nonnegative continuous observables vanishing at infinity, which is the form an analytic
construction produces, and is upgraded to all nonnegative measurable observables through the
potential measures.

The regularity data are an explicit hypothesis: positivity, contractivity and the resolvent
identity do not by themselves give the compactified semigroup a continuous-path process.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty



open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]









variable {X₀ X₁ : Type*}
  [MetricSpace X₀] [LocallyCompactSpace X₀] [SecondCountableTopology X₀]
  [MeasurableSpace X₀] [BorelSpace X₀]
  [MetricSpace X₁] [LocallyCompactSpace X₁] [SecondCountableTopology X₁]
  [MeasurableSpace X₁] [BorelSpace X₁]



open MarkovProcess.PositiveC0ContractiveResolvent in

theorem MarkovProcess.PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess (R₀ : PositiveC0ContractiveResolvent X₀)
    (R₁ : PositiveC0ContractiveResolvent X₁) (h₁ : R₁.OnePointRegular)
    {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota)
    (hcompat : IsPartProcess R₀ R₁ h₁ hiota)
    {lam : ℝ} (hlam : 0 < lam) {g : X₁ → ℝ≥0∞} (hg : Measurable g) (y : X₀) :
    R₀.kernelSemigroup.kernelResolvent lam (fun z ↦ g (iota z)) y ≤
      R₁.kernelSemigroup.kernelResolvent lam g (iota y) := by sorry
