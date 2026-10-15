-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_lintegral_gaussian_shift_scale
-- name    : OAI.NoiselessRegression.lintegral_gaussian_shift_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:27:54.705661+00:00
-- url     : https://prove2.me/theorems/74aefe3e-f364-4edd-959a-7806fd48ad05
-- title:
--   Change of variables for a shifted and rescaled standard Gaussian vector
-- statement:
--   Let $m\in\mathbb N$, let $\delta\in\mathbb R$ with $\delta\neq0$, let $a=(a_1,\dots,a_m)\in\mathbb R^m$, and let $f:\mathbb R^m\to[0,\infty]$ be measurable. Write $N(0,1)^{\otimes m}$ for the standard Gaussian measure on $\mathbb R^m$ (independent standard normal coordinates), and for $v>0$ let $g_v(x)=(2\pi v)^{-1/2}e^{-x^2/(2v)}$ be the centred normal density of variance $v$. Then
--
--   $$
--   \int_{\mathbb R^m}f\big(a+\delta u\big)\,dN(0,1)^{\otimes m}(u)\;=\;\int_{\mathbb R^m}\Big(\prod_{j=1}^{m}g_{\delta^2}(y_j-a_j)\Big)f(y)\,dy,
--   $$
--
--   where $dy$ is Lebesgue measure on $\mathbb R^m$; both sides may equal $+\infty$.
--
--   Equivalently, if $U$ is standard Gaussian in $\mathbb R^m$ then $a+\delta U$ has Lebesgue density $y\mapsto\prod_j g_{\delta^2}(y_j-a_j)$. In the regression setting, with $a=(\langle t,A_j\rangle)_{j\le m}$, this computes the law of labels corrupted by independent Gaussian noise of standard deviation $|\delta|$ as a density with respect to Lebesgue measure.
--
--   **Formalization Note** The density is Mathlib's `gaussianPDF 0 v` with the variance $v=\delta^2$ packaged as a nonnegative real number, and the integrals are lower Lebesgue integrals. The hypothesis $\delta\neq0$ is needed because for $\delta=0$ the left-hand side is $f(a)$, an integral against a point mass, which has no Lebesgue density.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Smoothing.lean#L123-L145

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u

theorem OAI.NoiselessRegression.lintegral_gaussian_shift_scale (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (a : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
      ∂Measure.pi (fun _ => gaussianReal 0 1) =
    ∫⁻ y : Fin m → ℝ, (∏ j, gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ)) (y j - a j)) * f y := by sorry
