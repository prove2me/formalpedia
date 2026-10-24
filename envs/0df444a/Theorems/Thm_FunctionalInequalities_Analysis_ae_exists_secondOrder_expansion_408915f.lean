-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_exists_secondOrder_expansion_408915f
-- name    : FunctionalInequalities.Analysis.ae_exists_secondOrder_expansion_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:04.169424+00:00
-- url     : https://prove2.me/theorems/f9460481-369e-4656-9cc8-8fea0d66d156
-- title:
--   Almost-Everywhere Alexandrov Expansion
-- statement:
--   This formalizes Alexandrov's second-order expansion theorem in the finite-dimensional inner-product setting.
--
--   Let $E$ be a finite-dimensional real inner-product space with measurable and Borel structures, and let $f:E\to\mathbb R$ be convex on all of $E$. For almost every $x$ with respect to Lebesgue measure, there exist $p\in E$ and a continuous linear map $B:E\to E$ such that:
--
--   1. $B$ is symmetric:
--      $$\langle Bv,w\rangle=\langle v,Bw\rangle\qquad(v,w\in E).$$
--   2. $p$ is the unique subgradient of $f$ at $x$.
--   3. For every $\varepsilon>0$, for all $y$ sufficiently near $x$,
--      $$\left|f(y)-f(x)-\langle p,y-x\rangle-\frac12\langle B(y-x),y-x\rangle\right|\le \varepsilon\|y-x\|^2.$$
--
--   The declaration `ae_exists_secondOrder_expansion` is the main almost-everywhere second-order expansion interface for later convex-analytic arguments. The almost-everywhere quantifier is with respect to `volume`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L596-L678 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, declaration `FunctionalInequalities.Analysis.ae_exists_secondOrder_expansion`; the repository is private at upload time).

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
section LT12D6AlexandrovTheorem
open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.ae_exists_secondOrder_expansion_408915f {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂(volume : Measure E), ∃ p : E, ∃ B : E →L[ℝ] E,
      (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
      (∀ q : E, (∀ y, f x + ⟪q, y - x⟫ ≤ f y) → q = p) ∧
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by sorry
