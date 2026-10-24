-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_le_integral_mul_sum_iteratedFDeriv_408915f
-- name    : FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:25.716977+00:00
-- url     : https://prove2.me/theorems/70f84b25-ee95-4477-9ec6-0fa583ac1d21
-- title:
--   Fatou Bound for Convex Second Differences
-- statement:
--   This is the Fatou bound for the distributional second derivatives of a convex function.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be convex, let $\iota$ be a finite type, let $v_i\in E$ and $c_i\geq0$ for $i\in\iota$. Let $\chi:E\to\mathbb R$ be nonnegative, $C^2$, and compactly supported. Let $g:E\to\mathbb R$ be almost everywhere strongly measurable. Assume that, almost everywhere in $x$, for every $\varepsilon>0$ there is $\delta>0$ such that for $0<t<\delta$,
--
--   $$
--   g(x)-\varepsilon\leq\sum_i c_i\frac{u(x+t v_i)+u(x-t v_i)-2u(x)}{t^2}.
--   $$
--
--   Then
--
--   $$
--   \int g\,\chi\,dx
--   \leq
--   \int u(x)\sum_i c_i\,D^2\chi(x)[v_i,v_i] \,dx.
--   $$
--
--   This is an auxiliary distributional inequality used to integrate lower bounds for second differences against nonnegative test functions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L459-L577 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, declaration `FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Filter
open scoped RealInnerProductSpace Topology
section LT12D7FatouSecondDifference
open MeasureTheory Set Filter
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv_408915f [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {ι : Type*} [Fintype ι] (v : ι → E) {c : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) {χ : E → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) {g : E → ℝ} (hgm : AEStronglyMeasurable g (volume : Measure E))
    (hg : ∀ᵐ x ∂(volume : Measure E), ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      g x - ε ≤ ∑ i, c i * ((u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2)) :
    ∫ x, g x * χ x ≤ ∫ x, u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i) := by sorry
