-- Prove2me | Theorems.Thm_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv
-- name    : MvPolynomial.logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/73a600d8-58df-5770-9055-f6e305071f3a
-- title:
--   Mahler measure by integrating out one variable
-- statement:
--   Let $n$ be a natural number and let $P \in \mathbb{C}[x_0,\dots,x_n]$, i.e. $P$ is an element of `MvPolynomial (Fin (n+1)) ℂ`. The assertion is an identity between two real numbers. On the left, `P.logMahlerMeasure` is $((2\pi)^{-1})^{n+1}$ times the integral of $\theta \mapsto \log\lVert P\bigl((\text{circleMap } 0\,1\,(\theta i))_{i}\bigr)\rVert$ over the box [`MvPolynomial.torusBox (n+1)`](def/MvPolynomial_LogMahlerMeasure.html#L16), that is over $\{\theta : \mathrm{Fin}(n+1) \to \mathbb{R} \mid \theta i \in (0,2\pi] \text{ for all } i\}$, the argument of $P$ being the point of the unit torus with coordinates $e^{i\theta i}$. On the right, $P$ is first transported by the isomorphism `MvPolynomial.finSuccEquiv ℂ n` to a one-variable polynomial over $\mathbb{C}[x_1,\dots,x_n]$ (singling out $x_0$ as the polynomial variable), its coefficients are then evaluated at the torus point $(e^{i\theta' i})_{i \in \mathrm{Fin}\,n}$, and Mathlib's one-variable $\log$ Mahler measure `Polynomial.logMahlerMeasure` of the resulting element of $\mathbb{C}[X]$ is integrated in $\theta'$ over [`MvPolynomial.torusBox n`](def/MvPolynomial_LogMahlerMeasure.html#L16), the result being multiplied by $((2\pi)^{-1})^{n}$. No nonvanishing hypothesis on $P$ is imposed.
--
--   This is the standard recursion expressing the multivariate logarithmic Mahler measure as the average over the $n$-dimensional torus of the one-variable Mahler measures of the fibre polynomials, and it is what allows statements about $m(P)$ to be reduced to the one-variable theory. It is used in the proof of the multivariate coefficient bound [`MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add`](thm.html#MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add), and relies on the integrability of $\log\lVert P\rVert$ on the torus recorded in [`MvPolynomial.integrableOn_log_norm_eval_circleMap`](thm.html#MvPolynomial.integrableOn_log_norm_eval_circleMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv.lean

import Definitions.Def_MvPolynomial_LogMahlerMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPolynomial.logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    P.logMahlerMeasure = ((2 * Real.pi)⁻¹) ^ n *
      ∫ θ' in MvPolynomial.torusBox n,
        (Polynomial.map (MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ' i)))
          (MvPolynomial.finSuccEquiv ℂ n P)).logMahlerMeasure := by sorry
