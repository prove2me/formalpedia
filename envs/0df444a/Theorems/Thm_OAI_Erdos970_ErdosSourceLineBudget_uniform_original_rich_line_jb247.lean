-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosSourceLineBudget_uniform_original_rich_line_jb247
-- name    : OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:43:38.897783+00:00
-- url     : https://prove2.me/theorems/5ae4aba9-3c11-4322-a034-1c39982a240a
-- title:
--   OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line` of [lean/OAI/NumberTheory/Jacobsthal/Estimates/NonstructuredCounts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Estimates/NonstructuredCounts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosSourceLineBudget`, with `open _root_.Filter`, `open scoped Topology`, `open ErdosInverseBoxHeight ErdosSourcePolynomial ErdosAuxiliaryPolynomial ErdosInversePrimeBin`, `open ErdosRichLine ErdosConvexGraph`):
--
--   ```lean
--   theorem uniform_original_rich_line_jb247 (C Cparent eta alpha c : ℝ)
--       (hC : 0 ≤ C) (hCp : 0 ≤ Cparent) (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
--       ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ ∀ S R p q xi : ℝ,
--         1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
--         1 ≤ S/q → S/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
--         z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 → p ≤ 2*R →
--         Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ Cparent →
--         ∀ (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ),
--           (∑ r : primeBin R xi, ((T r).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
--           ∀ X : Finset (ℤ × ℤ), (∀ v ∈ X, InSquare S v) →
--             Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) →
--             S/(sourceZ z)^4 ≤ (X.card : ℝ) → (∀ v ∈ X, RichPoint R xi c T a v) →
--             ∃ (l : PrimitiveIntegerLine) (Y : Finset (ℤ × ℤ)), Y ⊆ X ∧
--               S/(R*(sourceZ z)^6) < (Y.card : ℝ) ∧ (∀ v ∈ Y, l.Contains v) ∧
--               (l.denominator : ℝ) ≤ 2*S/(Y.card : ℝ) ∧
--               |(l.slope : ℝ)| ≤ 2*S/(Y.card : ℝ) ∧
--               |(l.intercept : ℝ)| ≤ 4*S^2/(Y.card : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.ErdosConvexGraph.InSquare`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceB`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceW`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceY`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceZ`, `OAI.Erdos970.ErdosInversePrimeBin.primeBin`, `OAI.Erdos970.ErdosRichLine.PrimitiveIntegerLine`, `OAI.Erdos970.ErdosSourceLineBudget.RichPoint` and `OAI.Erdos970.ErdosRichLine.PrimitiveIntegerLine.Contains` (definitions bundle `OAIQ247J003` of this split).
--
--   **Used by.** The proofs of `OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell_jb247` and `OAI_Erdos970_ErdosInverseStructured_uniform_no_rich_nonstructured_set_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Estimates/NonstructuredCounts.lean (declaration OAI.Erdos970.ErdosSourceLineBudget.uniform_original_rich_line)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
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
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight ErdosSourcePolynomial ErdosAuxiliaryPolynomial ErdosInversePrimeBin
open ErdosRichLine ErdosConvexGraph

theorem uniform_original_rich_line_jb247 (C Cparent eta alpha c : ℝ)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cparent) (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ ∀ S R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ S/q → S/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 → p ≤ 2*R →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ Cparent →
      ∀ (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ),
        (∑ r : primeBin R xi, ((T r).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        ∀ X : Finset (ℤ × ℤ), (∀ v ∈ X, InSquare S v) →
          Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) →
          S/(sourceZ z)^4 ≤ (X.card : ℝ) → (∀ v ∈ X, RichPoint R xi c T a v) →
          ∃ (l : PrimitiveIntegerLine) (Y : Finset (ℤ × ℤ)), Y ⊆ X ∧
            S/(R*(sourceZ z)^6) < (Y.card : ℝ) ∧ (∀ v ∈ Y, l.Contains v) ∧
            (l.denominator : ℝ) ≤ 2*S/(Y.card : ℝ) ∧
            |(l.slope : ℝ)| ≤ 2*S/(Y.card : ℝ) ∧
            |(l.intercept : ℝ)| ≤ 4*S^2/(Y.card : ℝ) := by
  sorry

end ErdosSourceLineBudget

end

end Erdos970

end OAI
end
