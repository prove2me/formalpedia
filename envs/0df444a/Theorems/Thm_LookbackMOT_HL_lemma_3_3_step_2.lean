-- Prove2me | Theorems.Thm_LookbackMOT_HL_lemma_3_3_step_2
-- name    : LookbackMOT.HL.lemma_3_3_step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:01.056233+00:00
-- url     : https://prove2.me/theorems/d8761f83-8e80-4e50-9c0a-d367ae904f2d
-- title:
--   Proof of Lemma 3.3, step (2), p. 17 — λ* ≥ 0 is measurable, μ-integrable and convex below r^μ
-- statement:
--   Let $\mu$ be an integrable probability measure on $\mathbb R$ with mean $X_0$, $b$ its barycenter function (3.9) with right-continuous inverse $b^{-1}$, and $\mu^{HL}$ its Hardy–Littlewood transform (3.12). Let $g:\mathbb R\to\mathbb R_+$ be $C^1$ and nondecreasing with $\mu^{HL}(g)<\infty$. Then the function
--   $$\lambda^*(x)=\int_{X_0<m<r^\mu}\frac{g'(m)\,(x-b^{-1}(m))^+}{m-b^{-1}(m)}\,dm$$
--   of (3.14) (the solution of (3.21) with $\psi=b^{-1}$) is nonnegative, measurable and $\mu$-integrable, and it is convex on $(-\infty,r^\mu)=\{x:\mu((x,\infty))>0\}$.
--
--   This is what step (2) of the proof of Lemma 3.3 establishes about $\lambda^*$ ("The convexity of $\lambda^*$ is obvious. Also, since $\lambda^*\ge0$, we only need to prove that $\lambda^*\in\mathbb L^1(\mu)$"); it makes $\mu(\lambda^*)$ in Theorem 3.1 a genuine finite integral.
--
--   **Formalization Note** The page concludes $\lambda^*\in\hat\Lambda^\mu_0$. As a real function on all of $\mathbb R$, $\lambda^*$ need not be convex beyond $r^\mu$: when $(\lambda^*)'$ blows up at $r^\mu$ (for example $\mu$ uniform on $[0,1]$ and $g(x)=x$) no finite convex extension exists, and the page defines $\lambda^*$ only for $x<r^\mu$. The statement therefore asserts convexity on $\{x:\mu((x,\infty))>0\}$ together with nonnegativity, measurability and integrability, which are the properties the page proves. The page's first sentence ("$\beta$ … solves the ODE (3.21)") is not stated: $\beta(m)<m$ fails off $[X_0,r^\mu)$, so $\beta\notin\Psi^{\lambda^*}$ in general. $\mu^{HL}(g)<\infty$ is integrability of $g$ under $\mu^{HL}$. $\lambda^*$ is written in the change-of-variables form of (3.14) (see the definitions item): the Lebesgue–Stieltjes reading of $b(d\xi)$ at the jumps of $b$ is not $\mu$-integrable for some $\mu$ with infinitely many atoms.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 17, step (2) of the proof of Lemma 3.3 (with (3.14), p. 12)

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem lemma_3_3_step_2 (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    Measurable (lamStar μ X₀ g) ∧ Integrable (lamStar μ X₀ g) μ ∧
      (∀ x, 0 ≤ lamStar μ X₀ g x) ∧
      ConvexOn ℝ {x : ℝ | 0 < μ (Set.Ioi x)} (lamStar μ X₀ g) := by sorry

end LookbackMOT.HL
