-- Prove2me | Theorems.Thm_MasulloGRH_prime_sums_converge_on_one_line
-- name    : MasulloGRH.prime_sums_converge_on_one_line
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:45:32.856111+00:00
-- url     : https://prove2.me/theorems/e94cf619-63fe-4a8b-ad37-e528f84cee0c
-- title:
--   Corollary B.7.2.3 — convergence of $\sum_{N(\mathfrak p)<x}\chi(\mathfrak p)N(\mathfrak p)^{-s}$ on the line $\operatorname{Re}(s)=1$
-- statement:
--   Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character. For a finite place $v$ let $\mathfrak p_v$ be its prime ideal, $q_v=N(\mathfrak p_v)$ its norm, and $\chi(\mathfrak p_v)=\chi_v(\pi_v)$ the value of $\chi$ at a uniformizer if $\chi$ is unramified at $v$ (and $0$ otherwise). $L_f(s,\chi)$ is the finite Hecke $L$-function, continued meromorphically to $\mathbb C$.
--
--   For real $x$ consider the finite sum over the prime ideals of norm less than $x$,
--   $$\Sigma_x(s)=\sum_{N(\mathfrak p)<x}\frac{\chi(\mathfrak p)}{N(\mathfrak p)^{s}} .$$
--
--   1. If $\chi$ is not trivial on $C_F^1$, then as $x\to+\infty$ the functions $\Sigma_x$ converge locally uniformly on the line $1+i\mathbb R$.
--   2. If $\chi=|\cdot|_F^{-it_0}$ for a real number $t_0$, then as $x\to+\infty$ the functions $\Sigma_x$ converge locally uniformly on $1+i(\mathbb R\setminus\{t_0\})$.
--
--   The prime sums converge on the edge of the half-plane of absolute convergence, except at the pole of $L_f(s,\chi)$.
--
--   **Formalization Note** Convergence is asserted to some limit function, which the source does not name. The ramified primes contribute $0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.7.2, Corollary B.7.2.3 (Uniform convergence away from the singularity - I), eq. (B.7.2.15), p. 651

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem prime_sums_converge_on_one_line
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (¬ χ.IsTrivialOnNormOne → ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) => ∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        χ.primeValue v * primeNorm v ^ (-s))
      g Filter.atTop {s : ℂ | s.re = 1}) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ → ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) => ∑ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        χ.primeValue v * primeNorm v ^ (-s))
      g Filter.atTop {s : ℂ | s.re = 1 ∧ s.im ≠ t₀}) := by sorry

end MasulloGRH
