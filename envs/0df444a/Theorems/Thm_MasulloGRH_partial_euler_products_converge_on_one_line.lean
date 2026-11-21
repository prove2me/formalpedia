-- Prove2me | Theorems.Thm_MasulloGRH_partial_euler_products_converge_on_one_line
-- name    : MasulloGRH.partial_euler_products_converge_on_one_line
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T03:45:55.455694+00:00
-- url     : https://prove2.me/theorems/809877ba-dbee-4b97-a5c3-34ff45a801ac
-- title:
--   Corollary B.7.2.5 — convergence of partial Euler products to $L_f(s,\chi)$ on the line $\operatorname{Re}(s)=1$
-- statement:
--   Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character. For a finite place $v$ let $\mathfrak p_v$ be its prime ideal, $q_v=N(\mathfrak p_v)$ its norm, and $\chi(\mathfrak p_v)=\chi_v(\pi_v)$ the value of $\chi$ at a uniformizer if $\chi$ is unramified at $v$ (and $0$ otherwise). $L_f(s,\chi)$ is the finite Hecke $L$-function, continued meromorphically to $\mathbb C$.
--
--   For real $x$ consider the partial Euler product over the prime ideals of norm less than $x$,
--   $$E_x(s)=\prod_{N(\mathfrak p)<x}\frac{1}{1-\chi(\mathfrak p)\,N(\mathfrak p)^{-s}} .$$
--
--   1. If $\chi$ is not trivial on $C_F^1$, then $E_x(s)\to L_f(s,\chi)$ as $x\to+\infty$, locally uniformly on the line $1+i\mathbb R$.
--   2. If $\chi=|\cdot|_F^{-it_0}$ for a real number $t_0$, then $E_x(s)\to L_f(s,\chi)$ as $x\to+\infty$, locally uniformly on $1+i(\mathbb R\setminus\{t_0\})$.
--
--   The Euler product, which defines $L_f(s,\chi)$ only for $\operatorname{Re}(s)>1$, still converges to the continued function on the boundary line, away from the pole. The draft uses this to divide by partial $L$-functions on the line $\operatorname{Re}(s)=1$.
--
--   **Formalization Note** The factors at ramified primes are $1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.7.2, Corollary B.7.2.5 (Convergence of partial Euler products on the 1-line), eq. (B.7.2.24), p. 653

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem partial_euler_products_converge_on_one_line
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (¬ χ.IsTrivialOnNormOne → TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) => ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        (eulerFactorInv χ v s)⁻¹)
      (heckeLFunction χ) Filter.atTop {s : ℂ | s.re = 1}) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ → TendstoLocallyUniformlyOn
      (fun (x : ℝ) (s : ℂ) => ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
        (eulerFactorInv χ v s)⁻¹)
      (heckeLFunction χ) Filter.atTop {s : ℂ | s.re = 1 ∧ s.im ≠ t₀}) := by sorry

end MasulloGRH
