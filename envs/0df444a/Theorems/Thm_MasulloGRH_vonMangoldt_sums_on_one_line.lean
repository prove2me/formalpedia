-- Prove2me | Theorems.Thm_MasulloGRH_vonMangoldt_sums_on_one_line
-- name    : MasulloGRH.vonMangoldt_sums_on_one_line
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T17:44:24.065125+00:00
-- url     : https://prove2.me/theorems/76c03547-6463-4bdb-b164-bdc2f62f8c70
-- title:
--   Theorem B.7.1.2 — Dirichlet polynomials of $L_f'(s,\chi)/L_f(s,\chi)$ on the line $\operatorname{Re}(s)=1$
-- statement:
--   Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character. For a finite place $v$ let $\mathfrak p_v$ be its prime ideal, $N(\mathfrak p_v)$ its norm, and $\chi(\mathfrak p_v)$ the value of $\chi$ at a uniformizer if $\chi$ is unramified at $v$ (and $0$ otherwise). Let $\Lambda_{F,\chi}$ be the twisted von Mangoldt function on the nonzero ideals of $\mathcal O_F$: $\Lambda_{F,\chi}(\mathfrak p^k)=\chi(\mathfrak p)^k\log N(\mathfrak p)$ for a prime power $\mathfrak p^k$, $k\ge 1$, and $\Lambda_{F,\chi}(I)=0$ if $I$ is not a prime power. For $\operatorname{Re}(s)>1$ the Dirichlet series $\sum_I\Lambda_{F,\chi}(I)N(I)^{-s}$ converges absolutely to $-L_f'(s,\chi)/L_f(s,\chi)$, where $L_f(s,\chi)$ is the finite Hecke $L$-function, continued meromorphically to $\mathbb C$.
--
--   For real $x$ consider its Dirichlet polynomial
--
--   $$B_x(s)=\sum_{0\ne I\subset\mathcal O_F,\ N(I)\le x}\frac{\Lambda_{F,\chi}(I)}{N(I)^{s}}.$$
--
--   1. If $\chi$ is not trivial on $C_F^1$, then as $x\to+\infty$,
--   $$B_x(s)\longrightarrow-\frac{L_f'(s,\chi)}{L_f(s,\chi)}$$
--   locally uniformly on the line $1+i\mathbb R$.
--
--   2. If $\chi=|\cdot|_F^{-it_0}$ for a real number $t_0$, so that $L_f(s,\chi)=\zeta_F(s-it_0)$, then as $x\to+\infty$,
--   $$B_x(s)-\frac{x^{1+it_0-s}}{1+it_0-s}\longrightarrow-\frac{L_f'(s,\chi)}{L_f(s,\chi)}=-\frac{\zeta_F'(s-it_0)}{\zeta_F(s-it_0)}$$
--   locally uniformly on $1+i(\mathbb R\setminus\{t_0\})$.
--
--   On the edge of the half-plane of absolute convergence the Dirichlet polynomials of $-L_f'/L_f$ still converge when $L_f(s,\chi)$ is entire, and oscillate with the explicit term $x^{1+it_0-s}/(1+it_0-s)$ of modulus $1/|t-t_0|$ when $L_f(s,\chi)$ has a pole at $1+it_0$. This is the input for the Abel summation that gives the convergence of the prime sums and of the partial Euler products on the 1-line (Theorem B.7.2.1, Corollaries B.7.2.3 and B.7.2.5).
--
--   **Formalization Note** The sum over the nonzero ideals $I$ with $N(I)\le x$ is written as the sum over the pairs $(v,k)$ of a finite place $v$ and an integer $k\ge1$ with $N(\mathfrak p_v)^k\le x$, which index the prime powers, on which $\Lambda_{F,\chi}$ is supported. The source states the limit along the set $J_b$ of real numbers $x$ that are integers or at distance at least $b>0$ from $\mathbb Z$; since $B_x=B_{\lfloor x\rfloor}$ and $x^{iu}-\lfloor x\rfloor^{iu}\to0$ uniformly for bounded $u$, this is equivalent to the limit over all real $x\to+\infty$ stated here. The remainder $f_x(s)$ of the source is the difference between the two sides. The estimate (B.7.1.9) at the point $s=1+it_0$ is not part of this statement. $L_f(s,\chi)$ is `heckeLFunction χ`, the continuation in normal form.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.7.1.3, Theorem B.7.1.2 (Convergence and oscillation on the 1-line), eqs. (B.7.1.8) and (B.7.1.10), pp. 645–646

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem vonMangoldt_sums_on_one_line
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (¬ χ.IsTrivialOnNormOne → TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) =>
        ∑ᶠ (p : HeightOneSpectrum (𝓞 F) × ℕ)
          (_ : 0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x),
          χ.primeValue p.1 ^ p.2 * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) : ℂ) *
            (primeNorm p.1 ^ p.2) ^ (-s))
      (fun s : ℂ => -(deriv (heckeLFunction χ) s / heckeLFunction χ s))
      Filter.atTop {s : ℂ | s.re = 1}) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ → TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) =>
        (∑ᶠ (p : HeightOneSpectrum (𝓞 F) × ℕ)
          (_ : 0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x),
          χ.primeValue p.1 ^ p.2 * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) : ℂ) *
            (primeNorm p.1 ^ p.2) ^ (-s)) -
          (x : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s))
      (fun s : ℂ => -(deriv (heckeLFunction χ) s / heckeLFunction χ s))
      Filter.atTop {s : ℂ | s.re = 1 ∧ s.im ≠ t₀}) := by sorry

end MasulloGRH
