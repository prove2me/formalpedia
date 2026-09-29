-- Prove2me | Theorems.Thm_MvPolynomial_integrableOn_log_norm_eval_circleMap
-- name    : MvPolynomial.integrableOn_log_norm_eval_circleMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/8a4f4d2a-6d21-5a73-8993-86494687ae97
-- title:
--   Integrability of log‖P‖ on the torus
-- statement:
--   For a natural number $n$ and a polynomial $P \in \mathbb{C}[x_0,\dots,x_{n-1}]$ in $n$ variables indexed by `Fin n`, the real-valued function sending $\theta : \mathrm{Fin}\,n \to \mathbb{R}$ to $\log \|P(\mathrm{circleMap}\,0\,1\,\theta_0, \dots)\|$, where the $i$-th variable is evaluated at the point $e^{i\theta_i}$ of the unit circle centred at $0$ of radius $1$, is integrable on the set [`MvPolynomial.torusBox n`](def/MvPolynomial_LogMahlerMeasure.html#L16), that is, on the product $\prod_{i \in \mathrm{Fin}\,n} (0, 2\pi]$ inside $\mathbb{R}^{\mathrm{Fin}\,n}$ with respect to Lebesgue measure. Integrability is in the sense of `MeasureTheory.IntegrableOn`: the function is measurable with respect to the restricted measure and has finite integral of its norm there, so $\int |\log \|P(e^{i\theta_0},\dots)\||\,d\theta < \infty$. No hypothesis $P \neq 0$ is imposed: for $P = 0$ the integrand is the constant $\log 0 = 0$ under the Lean convention for the logarithm at $0$, and for $P \neq 0$ the logarithmic singularities of the integrand along the intersection of the zero locus of $P$ with the torus are integrable.
--
--   This is the standard integrability statement underlying the logarithmic Mahler measure $m(P)$ of a multivariable polynomial, which makes the defining integral over $(0,2\pi]^n$ absolutely convergent. It is used in the inductive computation of $m(P)$ by integrating over one variable at a time, in the bound for $\log$ of a coefficient in terms of $m(P)$, and in the torus argument producing a point where a covector sum of logarithms is large.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_integrableOn_log_norm_eval_circleMap.lean

import Definitions.Def_MvPolynomial_LogMahlerMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPolynomial.integrableOn_log_norm_eval_circleMap {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    MeasureTheory.IntegrableOn
      (fun θ : Fin n → ℝ ↦ Real.log ‖MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P‖)
      (MvPolynomial.torusBox n) := by sorry
