-- Prove2me | Theorems.Thm_MasulloGRH_dirichlet_polynomials_on_one_line_of_region_bound
-- name    : MasulloGRH.dirichlet_polynomials_on_one_line_of_region_bound
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T18:04:30.793174+00:00
-- url     : https://prove2.me/theorems/9901c64a-457d-41ff-a2ac-44bad9cbeebc
-- title:
--   Proof of Theorem B.7.1.2 — Perron's formula on the line $\operatorname{Re}(s)=1$ for a Dirichlet series bounded in a zero-free region
-- statement:
--   Let $(a_n)_{n\ge1}$ be complex numbers with $|a_n|\le M\,\Lambda(n)$ for a constant $M$, where $\Lambda$ is the von Mangoldt function, and let $G$ be a function on $\mathbb C$ with
--
--   $$G(s)=\sum_{n\ge1}\frac{a_n}{n^{s}}\qquad(\operatorname{Re}(s)>1).$$
--
--   Let $t_0\in\mathbb R$, $r\in\mathbb C$, $c>0$ and $C$ be given, write $p=1+it_0$, and let $\mathcal R$ be the region of the points $s=\sigma+it$ with
--
--   $$\sigma\ge 1-\frac{c}{\log(|t|+3)} .$$
--
--   Assume that $G$ is analytic at every point of $\mathcal R\setminus\{p\}$ and that
--
--   $$\Bigl|G(s)-\frac{r}{s-p}\Bigr|\le C\,\log^2(|t|+3)\qquad(s\in\mathcal R\setminus\{p\}).$$
--
--   Then, as the integer $N\to\infty$,
--
--   $$\sum_{n=1}^{N}\frac{a_n}{n^{s}}-\frac{r\,N^{\,p-s}}{p-s}\longrightarrow G(s)$$
--
--   locally uniformly on $\{s:\operatorname{Re}(s)=1,\ s\ne p\}$.
--
--   So the Dirichlet polynomials of $G$ still converge on the edge of the half-plane of absolute convergence, up to the oscillating term $rN^{p-s}/(p-s)$ produced by a possible simple pole of $G$ at $p$ with residue $r$; when $r=0$ they converge to $G$. With $a_n$ the coefficients of $-L_f'(s,\chi)/L_f(s,\chi)$ and the classical zero-free region this is Theorem B.7.1.2 of the source.
--
--   **Formalization Note** This is the general statement behind the proof of Theorem B.7.1.2: the truncated Perron formula of Lemma B.7.1.1 (Titchmarsh, Lemma 3.12) applied to the coefficients $a_n$, followed by the contour shift into the region $\mathcal R$, where the hypotheses on $G$ replace the properties of $L_f'/L_f$ quoted there. Only integer cut-offs $N$ are used; the sum runs over $1\le n\le N$. The hypotheses do not require $G$ to be analytic at $p$ even when $r=0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.7.1.2–§B.7.1.3, Lemma B.7.1.1 and the proof of Theorem B.7.1.2, eqs. (B.7.1.11)–(B.7.1.15), pp. 644–648; E. C. Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., Ch. III, §3.12–§3.14

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

theorem dirichlet_polynomials_on_one_line_of_region_bound
    (a : ℕ → ℂ) (G : ℂ → ℂ) (M c C : ℝ) (r : ℂ) (t₀ : ℝ) (hc : 0 < c)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ M * ArithmeticFunction.vonMangoldt n)
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s)
    (han : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
      AnalyticAt ℂ G s)
    (hbd : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
      ‖G s - r / (s - (1 + t₀ * Complex.I))‖ ≤ C * Real.log (|s.im| + 3) ^ 2) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (s : ℂ) =>
        ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s) -
          r * (N : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s))
      G Filter.atTop {s : ℂ | s.re = 1 ∧ s.im ≠ t₀} := by sorry

end MasulloGRH
