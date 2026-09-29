-- Prove2me | Theorems.Thm_MvPolynomial_log_norm_coeff_le_logMahlerMeasure_add
-- name    : MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/9741f1bf-32da-598f-8994-831c8ba8904c
-- title:
--   Mahler's bound: coefficients versus logarithmic Mahler measure
-- statement:
--   Let $n$ be a natural number, let $P \in \mathbb{C}[x_i : i \in \mathrm{Fin}\,n]$ be a polynomial in $n$ commuting variables with complex coefficients, and let $m : \mathrm{Fin}\,n \to_{f} \mathbb{N}$ be a multi-index lying in the support of $P$, i.e. the coefficient of $x^m$ in $P$ is non-zero. Then
--   $$\log \lVert \operatorname{coeff}_m P \rVert \;\le\; \mathrm{m}(P) + \Bigl(\sum_{i} \deg_{x_i} P\Bigr)\log 2,$$
--   where $\deg_{x_i} P$ is `MvPolynomial.degreeOf i P`, the partial degree of $P$ in the variable $x_i$, the sum being over all $i \in \mathrm{Fin}\,n$ and taken as a real number, and where $\mathrm{m}(P) =$ `P.logMahlerMeasure` is by definition
--   $$(2\pi)^{-n} \int_{(0,2\pi]^n} \log \bigl\lVert P\bigl(e^{i\theta_0},\dots,e^{i\theta_{n-1}}\bigr)\bigr\rVert \, d\theta,$$
--   the integral being the Bochner integral of the stated function over the box [`MvPolynomial.torusBox n`](def/MvPolynomial_LogMahlerMeasure.html#L16), the product of $n$ copies of the interval $(0,2\pi]$, with respect to Lebesgue measure, and the evaluation being at the points $\mathrm{circleMap}\,0\,1\,(\theta_i) = e^{i\theta_i}$ of the unit circle. The support hypothesis is needed because in Lean $\log 0 = 0$.
--
--   This is Mahler's inequality bounding the naive height of a multivariable polynomial by its Mahler measure, the non-trivial half of the comparison $|\mathrm{m}(P) - \log H(P)| = O(\deg P)$. It is used in the construction of torus points with prescribed logarithmic growth, through [`Pencil.exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge`](thm.html#Pencil.exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge) and [`Pencil.exists_rootOfUnity_torus_covector_sum_log_ge`](thm.html#Pencil.exists_rootOfUnity_torus_covector_sum_log_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_log_norm_coeff_le_logMahlerMeasure_add.lean

import Definitions.Def_MvPolynomial_LogMahlerMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add {n : ℕ} (P : MvPolynomial (Fin n) ℂ) {m : Fin n →₀ ℕ} (hm : m ∈ P.support) :
    Real.log ‖MvPolynomial.coeff m P‖ ≤
      P.logMahlerMeasure + (∑ i, (MvPolynomial.degreeOf i P : ℝ)) * Real.log 2 := by sorry
