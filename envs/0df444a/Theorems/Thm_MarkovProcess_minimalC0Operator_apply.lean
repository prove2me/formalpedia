-- Prove2me | Theorems.Thm_MarkovProcess_minimalC0Operator_apply
-- name    : MarkovProcess.minimalC0Operator_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:27:17.021998+00:00
-- url     : https://prove2.me/theorems/fb2e93cc-4f2d-4719-964a-4a889370dd6d
-- title:
--   MarkovProcess: minimalC0Operator_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Killed_GluingC0_186c1e9f
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingMeasure_1a481231
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_GluingRealResolvent_55a9f996
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
# The supremum resolvent as a positive `C₀`-contractive resolvent

The supremum resolvent of a family of local resolvents acts on bounded measurable observables.
Two properties of its action on `C₀` are analytic and are hypotheses here: that the value on an
observable vanishing at infinity is again continuous and vanishing at infinity, supplied as a map
`T` together with the identification `hT` of its values, and that the range of `T` is dense.
Additivity, real homogeneity, the operator bound `1 / lam`, positivity and the resolvent identity
are then proved from the extended-real theory, and assemble the supremum resolvent into a
`PositiveC0ContractiveResolvent` (`minimalC0Resolvent`).

The semigroup which that resolvent generates is represented by a sub-Markov kernel semigroup, and
its kernel resolvent is the supremum resolvent again, on every nonnegative measurable observable
(`kernelResolvent_minimalC0Resolvent`): the two potential measures agree on continuous
observables vanishing at infinity, hence everywhere.

If in addition the shift times the supremum resolvent of the constant observable one is one, the
represented semigroup loses no mass (`isConservative_kernelSemigroup_minimalC0Resolvent`), and
the compactified process started at any point almost surely never reaches the added point
(`ae_exitTime_eq_top_minimalC0Resolvent`).  No kernel into the continuous paths of the state
space is produced from that statement.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  {X : ℕ → Type*} [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)



section Operator

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))









end Operator

section Identification

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))
  (hemb : ∀ m, MeasurableEmbedding (emb m))
  (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent R emb m nu h y)
  (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
    T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
  (hdense : ∀ nu, DenseRange (T nu))





end Identification

section Conservativity

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))
  (hemb : ∀ m, MeasurableEmbedding (emb m))
  (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent R emb m nu h y)
  (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
    T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
  (hdense : ∀ nu, DenseRange (T nu))





end Conservativity

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The supremum resolvent as a positive `C₀`-contractive resolvent

The supremum resolvent of a family of local resolvents acts on bounded measurable observables.
Two properties of its action on `C₀` are analytic and are hypotheses here: that the value on an
observable vanishing at infinity is again continuous and vanishing at infinity, supplied as a map
`T` together with the identification `hT` of its values, and that the range of `T` is dense.
Additivity, real homogeneity, the operator bound `1 / lam`, positivity and the resolvent identity
are then proved from the extended-real theory, and assemble the supremum resolvent into a
`PositiveC0ContractiveResolvent` (`minimalC0Resolvent`).

The semigroup which that resolvent generates is represented by a sub-Markov kernel semigroup, and
its kernel resolvent is the supremum resolvent again, on every nonnegative measurable observable
(`kernelResolvent_minimalC0Resolvent`): the two potential measures agree on continuous
observables vanishing at infinity, hence everywhere.

If in addition the shift times the supremum resolvent of the constant observable one is one, the
represented semigroup loses no mass (`isConservative_kernelSemigroup_minimalC0Resolvent`), and
the compactified process started at any point almost surely never reaches the added point
(`ae_exitTime_eq_top_minimalC0Resolvent`).  No kernel into the continuous paths of the state
space is produced from that statement.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  {X : ℕ → Type*} [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)




variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))



open MarkovProcess in
omit [LocallyCompactSpace alpha] [SecondCountableTopology alpha] in

@[simp]

theorem MarkovProcess.minimalC0Operator_apply (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
      T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
    (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) :
    minimalC0Operator R emb T hemb hmono hT nu f = T nu f := by sorry
