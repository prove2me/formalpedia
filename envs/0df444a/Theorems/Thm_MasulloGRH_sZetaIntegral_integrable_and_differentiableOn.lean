-- Prove2me | Theorems.Thm_MasulloGRH_sZetaIntegral_integrable_and_differentiableOn
-- name    : MasulloGRH.sZetaIntegral_integrable_and_differentiableOn
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:59.406064+00:00
-- url     : https://prove2.me/theorems/7d3e2ea2-69b4-4dc8-bcc6-2365ef54b1f4
-- title:
--   Theorem 3.3.1.1(1) — the $S$-local zeta integral $Z_S(f,c)=\int f\,c\,d\mu_S$ converges absolutely for $\sigma(c)>0$ and is holomorphic in $c$
-- statement:
--   **Convergence and holomorphy of the $S$-local zeta integrals** (Theorem 3.3.1.1(1) of the source; for a single place this is Tate's local zeta integral).
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$ be the ring of $S$-adeles, $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ the group of $S$-ideles with the $S$-idelic norm $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ (normalized absolute values), $\mu_S=\bigotimes_{v\in S}\mu_v$ the $S$-local multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbb A_{F,S})$, and $\mathcal S(\mathbb A_{F,S})$ the Schwartz–Bruhat space of $\mathbb A_{F,S}$. A *quasi-character* of $\mathrm{GL}_1(\mathbb A_{F,S})$ is a continuous homomorphism $c:\mathrm{GL}_1(\mathbb A_{F,S})\to\mathbb C^\times$; we assume that it has an *exponent* $\sigma\in\mathbb R$, i.e. $|c(g)|=|g|_{F,S}^{\sigma}$ for all $g$. Every quasi-character of $J_{F,S}=\mathrm{GL}_1(\mathbb A_{F,S})/\mathcal O_{F,S}^\times$ (the case of the source) has one, namely its abscissa $\sigma(c)$. For $f\in\mathcal S(\mathbb A_{F,S})$ put
--   $$Z_S(f,c)=\int_{\mathrm{GL}_1(\mathbb A_{F,S})}f(g)\,c(g)\,d\mu_S(g).$$
--
--   Let $c$ be a quasi-character of exponent $\sigma$. Then:
--
--   1. for every $s\in\mathbb C$ with $\sigma+\operatorname{Re}s>0$ the function $g\mapsto f(g)\,c(g)\,|g|_{F,S}^{s}$ is $\mu_S$-integrable;
--   2. the function $s\mapsto Z_S(f,c\,|\cdot|_{F,S}^{s})$ is holomorphic on the half-plane $\{\sigma+\operatorname{Re}s>0\}$.
--
--   Since $c\,|\cdot|_{F,S}^s$ has exponent $\sigma+\operatorname{Re}s$, and, writing $\Omega(J_{F,S})$ for the space of quasi-characters of $J_{F,S}$ and $\Omega(J_{F,S})_{>0}$ for those of exponent $>0$, for $c\in\Omega(J_{F,S})$ every quasi-character of exponent $>0$ in the connected component of $c$ in $\Omega(J_{F,S})$ is of this form, this says that $Z_S(f,c)$ converges absolutely on $\Omega(J_{F,S})_{>0}$ and is holomorphic there. It is the starting point of the $S$-local theory of the source (the "forward side" of the $S$-local Mellin transform), used in Chapters 3–5.
--
--   **Formalization Note.** A finite set $S\supseteq S_\infty$ of places is represented by the finite set `Sf` of its finite places. The function on the Riemann surface of quasi-characters is written in the coordinate $s$ of a component $\{c\,|\cdot|_{F,S}^s\}$, as in the platform statement of the global Theorem 3.2.2.1. The quasi-character is not required to be trivial on the $S$-units; the hypothesis $|c|=|\cdot|_{F,S}^\sigma$ replaces the abscissa. The local uniformity of the convergence on compact sets, asserted in the source, is not stated separately.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 129, Theorem 3.3.1.1(1), eq. (3.3.1.1) (proof pp. 129–130); classical reference cited in the proof: J. W. S. Cassels, A. Fröhlich (eds.), Algebraic Number Theory, Ch. XV (J. T. Tate, Fourier analysis in number fields and Hecke's zeta-functions), Definition 2.4.1 (local zeta integral)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sZetaIntegral_integrable_and_differentiableOn
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (f : SAdelicSchwartz F Sf) (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) :
    (∀ s : ℂ, 0 < σ + s.re →
      Integrable (fun g : SIdeleGroup F Sf => f.eval (g : SAdeleRing F Sf) * sQuasiTwist Sf c s g)
        (sMultiplicativeTamagawa F Sf)) ∧
    DifferentiableOn ℂ (fun s : ℂ => sZetaIntegral f (sQuasiTwist Sf c s))
      {s : ℂ | 0 < σ + s.re} := by sorry

end MasulloGRH
