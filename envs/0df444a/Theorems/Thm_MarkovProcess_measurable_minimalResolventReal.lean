-- Prove2me | Theorems.Thm_MarkovProcess_measurable_minimalResolventReal
-- name    : MarkovProcess.measurable_minimalResolventReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:27:18.579443+00:00
-- url     : https://prove2.me/theorems/48bb1a8f-4c01-4599-8106-e9e54817b89b
-- title:
--   MarkovProcess: measurable_minimalResolventReal
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Killed_GluingLinearity_fff8f190
import Definitions.Def_MarkovProcess_V3H_Killed_GluingRealResolvent_55a9f996
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
# The supremum resolvent on bounded real observables

The supremum resolvent of `Killed/GluingMinimal.lean` acts on nonnegative extended-real
observables.  On a bounded real observable it acts through the positive and negative parts,

  `R_lam f := (R_lam f⁺).toReal - (R_lam f⁻).toReal`   (`minimalResolventReal`),

which is well defined because a uniform bound `D` for the observable bounds both values by
`D / lam` (`Killed/GluingLinearity.lean`).  The real form is measurable in the starting point
(`measurable_minimalResolventReal`), obeys the same uniform bound
(`abs_minimalResolventReal_le`), is additive and real homogeneous on bounded measurable
observables (`minimalResolventReal_add`, `minimalResolventReal_smul`), satisfies the
resolvent equation (`minimalResolventReal_resolventEquation`), and commutes at two shifts
(`minimalResolventReal_comm`).

Additivity, and with it the resolvent equation, is available exactly when the transported
resolvents are monotone in the index; that monotonicity is a bare hypothesis here.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)



section Bounds








end Bounds

section Elementary


















end Elementary

section Additive














end Additive

section ResolventEquation








end ResolventEquation

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The supremum resolvent on bounded real observables

The supremum resolvent of `Killed/GluingMinimal.lean` acts on nonnegative extended-real
observables.  On a bounded real observable it acts through the positive and negative parts,

  `R_lam f := (R_lam f⁺).toReal - (R_lam f⁻).toReal`   (`minimalResolventReal`),

which is well defined because a uniform bound `D` for the observable bounds both values by
`D / lam` (`Killed/GluingLinearity.lean`).  The real form is measurable in the starting point
(`measurable_minimalResolventReal`), obeys the same uniform bound
(`abs_minimalResolventReal_le`), is additive and real homogeneous on bounded measurable
observables (`minimalResolventReal_add`, `minimalResolventReal_smul`), satisfies the
resolvent equation (`minimalResolventReal_resolventEquation`), and commutes at two shifts
(`minimalResolventReal_comm`).

Additivity, and with it the resolvent equation, is available exactly when the transported
resolvents are monotone in the index; that monotonicity is a bare hypothesis here.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)














open MarkovProcess in

theorem MarkovProcess.measurable_minimalResolventReal (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (minimalResolventReal R emb lam f) := by sorry
