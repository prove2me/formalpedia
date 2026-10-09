-- Prove2me | Theorems.Thm_MeasureTheory_integral_mul_fderiv_eq_neg_fderiv_mul_of_local_contDiff_ball
-- name    : MeasureTheory.integral_mul_fderiv_eq_neg_fderiv_mul_of_local_contDiff_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T10:21:14.433256+00:00
-- url     : https://prove2.me/theorems/55e05ec3-c15d-446b-abbf-cac864cb7412
-- title:
--   Integration by parts with a cutoff under local C¹ regularity on a ball
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with additive Haar measure $\mu$. Let $f,g:E\to\mathbb R$, and suppose $f$ is continuously differentiable near every point of a closed ball $\overline B_r(x)$. Suppose $g$ is continuously differentiable on $E$ and its topological support lies in that closed ball. Then, for every $v\in E$,
--
--   $$\int_E g(y)Df(y)[v]\,d\mu(y)=-\int_E f(y)Dg(y)[v]\,d\mu(y).$$
--
--   This form of integration by parts permits localized arguments when the unweighted function has no regularity or integrability assumptions outside the ball.
-- source:
--   Mathlib Analysis/Calculus/LineDeriv/IntegrationByParts.lean, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable; compact-support specialization developed for Hunter, Notes on PDEs, printed pp. 17–18, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory MeasureTheory.Measure Set Metric Filter Function
open scoped Topology
set_option autoImplicit false

theorem MeasureTheory.integral_mul_fderiv_eq_neg_fderiv_mul_of_local_contDiff_ball {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {f g : E → ℝ} {x : E} {r : ℝ}
    (hf : ∀ y ∈ closedBall x r, ContDiffAt ℝ 1 f y)
    (hg : ContDiff ℝ 1 g) (hgs : tsupport g ⊆ closedBall x r) (v : E) :
    (∫ y, g y * fderiv ℝ f y v ∂μ) = -(∫ y, f y * fderiv ℝ g y v ∂μ) := by sorry
