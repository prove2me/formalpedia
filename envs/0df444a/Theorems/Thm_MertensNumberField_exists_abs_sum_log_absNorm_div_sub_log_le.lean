-- Prove2me | Theorems.Thm_MertensNumberField_exists_abs_sum_log_absNorm_div_sub_log_le
-- name    : MertensNumberField.exists_abs_sum_log_absNorm_div_sub_log_le
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:36.715767+00:00
-- url     : https://prove2.me/theorems/73c77a9e-2c2c-49bf-847d-1955b354623f
-- title:
--   Mertens' first theorem for number fields — $\sum_{N(\mathfrak p^k)\le x}\log N(\mathfrak p)/N(\mathfrak p)^k=\log x+O(1)$
-- statement:
--   **Mertens' first theorem for number fields (von Mangoldt form).** Let $F$ be a number field with ring of integers $\mathcal O_F$. For a nonzero ideal $I\subset\mathcal O_F$ let $N(I)=[\mathcal O_F:I]$ be its absolute norm, and let $\Lambda_F$ be the von Mangoldt function of $F$ (eq. (B.6.1.13) of the source):
--   $$\Lambda_F(I)=\begin{cases}\log N(\mathfrak p),& I=\mathfrak p^k\ \text{a power of a prime ideal},\ k\ge1,\\ 0,&\text{otherwise.}\end{cases}$$
--   Then there is a constant $C=C_F$ such that for every real $x\ge1$
--   $$\Bigl|\sum_{0\ne I\subset\mathcal O_F,\ N(I)\le x}\frac{\Lambda_F(I)}{N(I)}-\log x\Bigr|\le C,$$
--   that is,
--   $$\sum_{\mathfrak p,\ k\ge1,\ N(\mathfrak p)^k\le x}\frac{\log N(\mathfrak p)}{N(\mathfrak p)^{k}}=\log x+O(1).$$
--
--   This is equation (B.7.1.9) of Theorem B.7.1.2(1) of the source. There it is written for the character $\chi=|\cdot|_F^{-it_0}$ at the point $s=1+it_0$ with the twisted function $\Lambda_{F,\chi}=\chi\Lambda_F$; since $\chi(\mathfrak p^k)N(\mathfrak p^k)^{-1-it_0}=N(\mathfrak p)^{-k}$, the left side does not depend on $t_0$ and (B.7.1.9) is the displayed estimate. For $F=\mathbb Q$ it is Mertens' first theorem $\sum_{n\le x}\Lambda(n)/n=\log x+O(1)$. The source obtains it from the behaviour of the Dirichlet polynomials of $\zeta_F'/\zeta_F$ on the line $\operatorname{Re}(s)=1$ and uses it to derive Mertens' product theorem for $F$ (Remark B.7.2.6).
--
--   **Formalization Note.** The statement uses Mathlib only. The sum over the nonzero ideals $I$ with $N(I)\le x$, on which $\Lambda_F$ is supported on prime powers, is written as a finite sum (`finsum`) over the pairs $(v,k)$ of a nonzero prime ideal $v$ of $\mathcal O_F$ (`HeightOneSpectrum (𝓞 F)`) and an integer $k\ge1$ with $N(\mathfrak p_v)^k\le x$; this is the indexing used by the platform theorem `MasulloGRH.vonMangoldt_sums_on_one_line` for (B.7.1.8), whose statement does not include (B.7.1.9). The "$O(1)$" of the source (for $x>1$) is the existence of a bound valid for all $x\ge1$; for $1\le x<2$ the sum is empty.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 645, Theorem B.7.1.2(1) (Convergence and oscillation on the 1-line), eq. (B.7.1.9)

import Mathlib

open Filter Topology NumberField IsDedekindDomain

set_option autoImplicit false

namespace MertensNumberField

theorem exists_abs_sum_log_absNorm_div_sub_log_le (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(∑ᶠ (p : HeightOneSpectrum (𝓞 F) × ℕ)
          (_ : 0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x),
          Real.log (Ideal.absNorm p.1.asIdeal : ℝ) / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2) -
        Real.log x| ≤ C := by sorry

end MertensNumberField
