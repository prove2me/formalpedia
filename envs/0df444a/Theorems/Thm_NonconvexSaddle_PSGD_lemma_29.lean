-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_29
-- name    : NonconvexSaddle.PSGD.lemma_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:59.796026+00:00
-- url     : https://prove2.me/theorems/47f0a9c6-06a8-430e-a4e2-7a62485a865a
-- title:
--   Lemma 29 — $\beta(t)/\sqrt3\le\alpha(t)\le\beta(t)$
-- statement:
--   Let $a=\eta\gamma\in(0,1]$ and define
--   $$\alpha(t)=\Big[\sum_{\tau=0}^{t-1}(1+a)^{2(t-1-\tau)}\Big]^{1/2},\qquad \beta(t)=\frac{(1+a)^t}{\sqrt{2a}}.$$
--   Then (1) $\alpha(t)\le\beta(t)$ for every $t\in\mathbb N$, and (2) $\alpha(t)\ge\beta(t)/\sqrt3$ for every $t\in\mathbb N$ with $t\ge\ln(2)/a$.
--
--   $\alpha(t)$ is, up to the factor $2\eta r/\sqrt d$, the standard deviation of the perturbation term $q_p(t)$ along $e_1$; the lemma says it grows like $(1+\eta\gamma)^t$.
--
--   **Formalization Note** The page allows $\eta\gamma\in[0,1]$; at $\eta\gamma=0$ the paper's $\beta(t)$ is $+\infty$, while Lean's $1/\sqrt0=0$ would make part (1) false for $t\ge1$, so $\eta\gamma>0$ is required. Lemmas 30 and 31 apply the lemma with $\eta\gamma>0$.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 26, Lemma 29

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 29 (arXiv:1902.04811v2, App. B.3, p. 26), with `a = ηγ ∈ (0, 1]`:
(1) `α(t) ≤ β(t)` for every `t ∈ ℕ`, and (2) `α(t) ≥ β(t)/√3` for `t ≥ ln 2/(ηγ)`. -/
theorem lemma_29 (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∀ t : ℕ, alphaL a t ≤ betaL a t) ∧
      ∀ t : ℕ, Real.log 2 / a ≤ (t : ℝ) → betaL a t / Real.sqrt 3 ≤ alphaL a t := by sorry

end NonconvexSaddle.PSGD
