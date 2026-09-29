-- Prove2me | Theorems.Thm_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero
-- name    : MvPolynomial.ae_restrict_torusBox_eval_circleMap_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/053c28cf-4416-5d58-a266-6f33e39bb709
-- title:
--   Non-zero polynomials vanish almost nowhere on the torus
-- statement:
--   Let $n$ be a natural number and let $P$ be a non-zero element of the polynomial ring $\mathbb{C}[x_i : i \in \mathrm{Fin}\,n]$ (`MvPolynomial (Fin n) ℂ`). The assertion is that, for Lebesgue measure on $\mathrm{Fin}\,n \to \mathbb{R}$ restricted to the box [`MvPolynomial.torusBox n`](def/MvPolynomial_LogMahlerMeasure.html#L16), that is to the product $\prod_{i} (0, 2\pi]$ of half-open intervals, almost every $\theta$ satisfies $$\mathrm{eval}\bigl(i \mapsto \mathrm{circleMap}\,0\,1\,(\theta i)\bigr)\,P \neq 0,$$ where $\mathrm{circleMap}\,0\,1\,(\theta i) = e^{\mathrm{i}\theta_i}$ is the point of the unit circle centred at $0$ with parameter $\theta_i$. Equivalently, the set of parameters $\theta \in (0,2\pi]^n$ for which $P(e^{\mathrm{i}\theta_1},\dots,e^{\mathrm{i}\theta_n})$ vanishes is Lebesgue-null; in the case $n = 0$ the statement reduces to the fact that a non-zero constant is non-zero.
--
--   This is the statement that an algebraic hypersurface meets the compact torus $(S^1)^n$ in a set of Haar measure zero, in the parametrised form used for the logarithmic Mahler measure of a multivariate polynomial. It underlies the integrability of $\log\|P\|$ over the torus, the comparison of the coefficients of $P$ with its logarithmic Mahler measure, and a lower bound for sums of logarithms at roots of unity in the theory of pencils.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero.lean

import Definitions.Def_MvPolynomial_LogMahlerMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPolynomial.ae_restrict_torusBox_eval_circleMap_ne_zero {n : ℕ} {P : MvPolynomial (Fin n) ℂ} (hP : P ≠ 0) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (MvPolynomial.torusBox n)),
      MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P ≠ 0 := by sorry
