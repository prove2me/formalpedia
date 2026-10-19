-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_lintegral_gaussian_shift_scale
-- name    : OAI.SubsphereRegression.lintegral_gaussian_shift_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:14:38.841981+00:00
-- url     : https://prove2.me/theorems/22f3fb52-01ff-4feb-a21d-12687aaf098e
-- title:
--   Density of a shifted and scaled standard Gaussian vector
-- statement:
--   Let $m\ge0$ be an integer, $\delta\in\mathbb{R}$ with $\delta\ne0$, $a=(a_1,\dots,a_m)\in\mathbb{R}^m$, and let $f:\mathbb{R}^m\to[0,\infty]$ be measurable. Write $N(0,1)^{\otimes m}$ for the standard Gaussian law on $\mathbb{R}^m$ (independent standard normal coordinates) and, for $v>0$, let
--   $$g_v(x)=\frac{1}{\sqrt{2\pi v}}\,e^{-x^2/(2v)}$$
--   be the density of the normal law $N(0,v)$ on $\mathbb{R}$. Then
--   $$\int_{\mathbb{R}^m}f(a+\delta u)\,dN(0,1)^{\otimes m}(u)=\int_{\mathbb{R}^m}\Bigl(\prod_{j=1}^mg_{\delta^2}(y_j-a_j)\Bigr)f(y)\,dy .$$
--
--   In words, if $Z$ is a standard Gaussian vector in $\mathbb{R}^m$, then $a+\delta Z$ has density $y\mapsto\prod_jg_{\delta^2}(y_j-a_j)$ with respect to Lebesgue measure, i.e. its law is $N(a,\delta^2I_m)$. This identity is used to compute the density of labels corrupted by Gaussian noise of level $\delta$.
--
--   **Formalization Note** The integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions, and $g_{\delta^2}$ is `gaussianPDF 0 v` with variance `v = δ^2` as a nonnegative real. The hypothesis $\delta\ne0$ is needed because Mathlib's normal law with variance $0$ is a Dirac mass, which has no density.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gaussian.lean#L347-L369

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace

theorem OAI.SubsphereRegression.lintegral_gaussian_shift_scale (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (a : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
      ∂Measure.pi (fun _ => gaussianReal 0 1) =
    ∫⁻ y : Fin m → ℝ, (∏ j, gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ)) (y j - a j)) * f y := by sorry
