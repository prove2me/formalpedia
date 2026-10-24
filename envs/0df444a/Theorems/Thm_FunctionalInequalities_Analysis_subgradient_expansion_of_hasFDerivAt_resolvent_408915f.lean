-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradient_expansion_of_hasFDerivAt_resolvent_408915f
-- name    : FunctionalInequalities.Analysis.subgradient_expansion_of_hasFDerivAt_resolvent_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:09.332199+00:00
-- url     : https://prove2.me/theorems/62910b45-c216-489f-af29-306f2b7625f2
-- title:
--   Subgradient Expansion at an Invertibly Differentiable Resolvent
-- statement:
--   This is an auxiliary local inverse-resolvent statement for convex subgradients.
--
--   Let $E$ be a real inner-product space, let $f:E\to\mathbb R$ and $P:E\to E$, and assume
--
--   $$f(Pz)+\langle z-Pz,y-Pz\rangle\le f(y)\qquad(z,y\in E).$$
--
--   Fix $z\in E$ and let $T:E\to E$ be a continuous linear equivalence such that $P$ is Fréchet differentiable at $z$ with derivative $T$. Then:
--
--   1. The only subgradient of $f$ at $Pz$ is $z-Pz$.
--   2. For every $\varepsilon>0$, for all $y$ sufficiently near $Pz$, every subgradient $q$ of $f$ at $y$ satisfies
--      $$\left\|q-(z-Pz)-\left(T^{-1}(y-Pz)-(y-Pz)\right)\right\|\le \varepsilon\|y-Pz\|.$$
--
--   The declaration `subgradient_expansion_of_hasFDerivAt_resolvent` is a local quantitative description of the subdifferential near the image point of an invertibly differentiable resolvent.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L147-L246 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, declaration `FunctionalInequalities.Analysis.subgradient_expansion_of_hasFDerivAt_resolvent`; the repository is private at upload time).

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
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.subgradient_expansion_of_hasFDerivAt_resolvent_408915f {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E} {T : E ≃L[ℝ] E}
    (hT : HasFDerivAt P (T : E →L[ℝ] E) z) :
    (∀ q : E, (∀ y, f (P z) + ⟪q, y - P z⟫ ≤ f y) → q = z - P z) ∧
    ∀ ε > 0, ∀ᶠ y in 𝓝 (P z), ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
      ‖q - (z - P z) - (T.symm (y - P z) - (y - P z))‖ ≤ ε * ‖y - P z‖ := by sorry
