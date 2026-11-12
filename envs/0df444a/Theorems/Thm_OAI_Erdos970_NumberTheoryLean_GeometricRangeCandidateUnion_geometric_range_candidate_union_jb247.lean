-- Prove2me | Theorems.Thm_OAI_Erdos970_NumberTheoryLean_GeometricRangeCandidateUnion_geometric_range_candidate_union_jb247
-- name    : OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:02.380834+00:00
-- url     : https://prove2.me/theorems/40dbe087-3825-41ba-9862-b206d076fadf
-- title:
--   OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union` of [lean/OAI/NumberTheory/Jacobsthal/Partitions/SourceRawBoxFactory.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Partitions/SourceRawBoxFactory.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion`, with `open scoped _root_.Erdos970`, `open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership`, `open GeometricBoxImages BoundedEdgeBins ParentCofactorChoices`, `open JacobsthalSourceScale`, `open CandidateExceptionMass BoundedCandidateCount`, `open BoxWitnessFactorization CanonicalSubsetBox ErdosInverseSampleCost`, `open ErdosCofactorChoices ErdosSubsetWord ErdosInverseBoxApplication`, `open LogarithmicBinScale LogarithmicBinEndpoints`, `open scoped Topology`):
--
--   ```lean
--   theorem geometric_range_candidate_union_jb247 (C Kstar aStar alpha delta sigma : ℝ)
--       (hC : 1 ≤ C) (hKstar : 0 ≤ Kstar) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
--       (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) :
--       ∃ cp : ℝ,0 < cp ∧ ∃ F : ℕ,∃ xi₀ : ℝ,0 < xi₀ ∧ xi₀ ≤ 1 ∧
--       ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ → ∀ᶠ top : ℝ in atTop,
--         ∃ hw : 1 < ErdosInverseBoxHeight.sourceW top,∃ htop : ErdosInverseBoxHeight.sourceW top < top,
--         ∀ R L : ℝ,∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → Consistent z →
--           z.cutoff=ErdosInverseBoxHeight.sourceB top → z.closed=true →
--           z.gap=Real.log (ErdosInverseBoxHeight.sourceY top:ℝ)/Real.log (ErdosInverseBoxHeight.sourceW top)-aStar+2 →
--         ∀ m ∈ geometricBoxes hw htop hxi C (ErdosInverseBoxHeight.sourceB top) R L alpha (1/100) z,
--         ∃ i : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),m i=1 ∧
--         top^alpha ≤ lower (ErdosInverseBoxHeight.sourceW top) top xi i ∧
--         lower (ErdosInverseBoxHeight.sourceW top) top xi i ≤ top^((1:ℝ)/100) ∧
--         (∀ j : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),
--           boundedEdgeBin (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m
--             (2*Kstar+3) (2*Kstar+3) j → ∀ residue : ℕ → ℕ,
--           j < i ∧ m j=1 ∧
--           let cm := parentCofactorMultiplicity m i j
--           let w := ErdosInverseBoxHeight.sourceW top
--           SourceInverseConclusion (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊)
--             residue delta (SmallSieveFinite.smallEuler ⌊w⌋₊) (cofactorScale top xi cm)
--             (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp sigma F
--             (actualBins top xi i) (cofactorChoices (actualBins top xi) cm) (actualBins top xi j) ∧
--           selectionWitnessMass (actualBins top xi) m i j
--             (actualWitness (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue delta
--               (SmallSieveFinite.smallEuler ⌊w⌋₊) (actualBins top xi i) (cofactorScale top xi cm)
--               (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp) ≤ sigma*selectionMass (actualBins top xi) m ) ∧ ∀ residue : ℕ → ℕ,
--           someWitnessMass (actualBins top xi) m i
--             (candidateBins (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m (2*Kstar+3) (2*Kstar+3))
--             (fun j => actualWitness (ErdosInverseBoxHeight.sourceY top)
--               (LargePrimeDeletion.cutoffPrimes ⌊ErdosInverseBoxHeight.sourceW top⌋₊) residue delta
--               (SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊) (actualBins top xi i)
--               (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (ErdosInverseBoxHeight.sourceW top) top xi i)
--               (ErdosInverseBoxHeight.sourceZ top) cp) ≤ (⌈2*Kstar+3⌉₊:ℝ)*sigma*selectionMass (actualBins top xi) m
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.NumberTheoryLean.FinitePathGeometry.Side` (definitions bundle `OAIQ247J001` of this split); `OAI.Erdos970.ErdosCofactorChoices.actualBins`, `OAI.Erdos970.ErdosCofactorChoices.cofactorChoices`, `OAI.Erdos970.ErdosCofactorChoices.cofactorScale`, `OAI.Erdos970.ErdosInverseBoxApplication.SourceInverseConclusion`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceB`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceW`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceY`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceZ`, `OAI.Erdos970.ErdosInverseSampleCost.actualWitness`, `OAI.Erdos970.NumberTheoryLean.BoundedCandidateCount.candidateBins`, `OAI.Erdos970.NumberTheoryLean.BoundedEdgeBins.boundedEdgeBin`, `OAI.Erdos970.NumberTheoryLean.BoxWitnessFactorization.selectionWitnessMass`, `OAI.Erdos970.NumberTheoryLean.CandidateExceptionMass.someWitnessMass`, `OAI.Erdos970.NumberTheoryLean.CanonicalSubsetBox.selectionMass`, `OAI.Erdos970.NumberTheoryLean.LargePrimeDeletion.cutoffPrimes`, `OAI.Erdos970.NumberTheoryLean.LogarithmicBinEndpoints.lower`, `OAI.Erdos970.NumberTheoryLean.LogarithmicBinScale.binCount` and `OAI.Erdos970.NumberTheoryLean.SmallSieveFinite.smallEuler` (definitions bundle `OAIQ247J003` of this split); `OAI.Erdos970.NumberTheoryLean.ParentCofactorChoices.parentCofactorMultiplicity` and `OAI.Erdos970.NumberTheoryLean.PrimeHistories.Node` (definitions bundle `OAIQ247J007` of this split); `OAI.Erdos970.NumberTheoryLean.GeometricBoxImages.geometricBoxes` and `OAI.Erdos970.NumberTheoryLean.PrimeBinMembership.Consistent` (definitions bundle `OAIQ247J010` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.ErdosVarianceFactory.source_raw_box_factory_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Partitions/SourceRawBoxFactory.lean (declaration OAI.Erdos970.NumberTheoryLean.GeometricRangeCandidateUnion.geometric_range_candidate_union)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

namespace NumberTheoryLean.GeometricRangeCandidateUnion
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open GeometricBoxImages BoundedEdgeBins ParentCofactorChoices
open JacobsthalSourceScale
open CandidateExceptionMass BoundedCandidateCount
open BoxWitnessFactorization CanonicalSubsetBox ErdosInverseSampleCost
open ErdosCofactorChoices ErdosSubsetWord ErdosInverseBoxApplication
open LogarithmicBinScale LogarithmicBinEndpoints
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem geometric_range_candidate_union_jb247 (C Kstar aStar alpha delta sigma : ℝ)
    (hC : 1 ≤ C) (hKstar : 0 ≤ Kstar) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) :
    ∃ cp : ℝ,0 < cp ∧ ∃ F : ℕ,∃ xi₀ : ℝ,0 < xi₀ ∧ xi₀ ≤ 1 ∧
    ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ → ∀ᶠ top : ℝ in atTop,
      ∃ hw : 1 < ErdosInverseBoxHeight.sourceW top,∃ htop : ErdosInverseBoxHeight.sourceW top < top,
      ∀ R L : ℝ,∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → Consistent z →
        z.cutoff=ErdosInverseBoxHeight.sourceB top → z.closed=true →
        z.gap=Real.log (ErdosInverseBoxHeight.sourceY top:ℝ)/Real.log (ErdosInverseBoxHeight.sourceW top)-aStar+2 →
      ∀ m ∈ geometricBoxes hw htop hxi C (ErdosInverseBoxHeight.sourceB top) R L alpha (1/100) z,
      ∃ i : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),m i=1 ∧
      top^alpha ≤ lower (ErdosInverseBoxHeight.sourceW top) top xi i ∧
      lower (ErdosInverseBoxHeight.sourceW top) top xi i ≤ top^((1:ℝ)/100) ∧
      (∀ j : Fin (binCount (ErdosInverseBoxHeight.sourceW top) top xi),
        boundedEdgeBin (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m
          (2*Kstar+3) (2*Kstar+3) j → ∀ residue : ℕ → ℕ,
        j < i ∧ m j=1 ∧
        let cm := parentCofactorMultiplicity m i j
        let w := ErdosInverseBoxHeight.sourceW top
        SourceInverseConclusion (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊)
          residue delta (SmallSieveFinite.smallEuler ⌊w⌋₊) (cofactorScale top xi cm)
          (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp sigma F
          (actualBins top xi i) (cofactorChoices (actualBins top xi) cm) (actualBins top xi j) ∧
        selectionWitnessMass (actualBins top xi) m i j
          (actualWitness (ErdosInverseBoxHeight.sourceY top) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) residue delta
            (SmallSieveFinite.smallEuler ⌊w⌋₊) (actualBins top xi i) (cofactorScale top xi cm)
            (lower w top xi i) (ErdosInverseBoxHeight.sourceZ top) cp) ≤ sigma*selectionMass (actualBins top xi) m ) ∧ ∀ residue : ℕ → ℕ,
        someWitnessMass (actualBins top xi) m i
          (candidateBins (ErdosInverseBoxHeight.sourceW top) top xi (ErdosInverseBoxHeight.sourceY top) m (2*Kstar+3) (2*Kstar+3))
          (fun j => actualWitness (ErdosInverseBoxHeight.sourceY top)
            (LargePrimeDeletion.cutoffPrimes ⌊ErdosInverseBoxHeight.sourceW top⌋₊) residue delta
            (SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW top⌋₊) (actualBins top xi i)
            (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (ErdosInverseBoxHeight.sourceW top) top xi i)
            (ErdosInverseBoxHeight.sourceZ top) cp) ≤ (⌈2*Kstar+3⌉₊:ℝ)*sigma*selectionMass (actualBins top xi) m := by
  sorry
end NumberTheoryLean.GeometricRangeCandidateUnion

open _root_.Filter

end Erdos970

end OAI
end
