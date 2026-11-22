-- Prove2me | Theorems.Thm_MasulloGRH_sLocalRho_mul_dual_and_conj
-- name    : MasulloGRH.sLocalRho_mul_dual_and_conj
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:25:04.572159+00:00
-- url     : https://prove2.me/theorems/7b003e87-d4f0-4db3-82a2-0cd55f370879
-- title:
--   Proposition 3.3.1.5(1)–(2) — $\rho_S(c)\,\rho_S(\widehat c)=c(-1)$, $\rho_S(\bar c)=c(-1)\,\overline{\rho_S(c)}$, and $|\rho_S(c)|=1$ on the line $\sigma(c)=\tfrac12$
-- statement:
--   **Symmetries of the factor $\rho_S$ of the $S$-local functional equation** (Proposition 3.3.1.5(1)–(2), eqs. (3.3.1.8)–(3.3.1.9), of the source; Tate's lemma on $\rho(c)$, for the product $\prod_{v\in S}F_v$).
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$ be the ring of $S$-adeles, $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ the group of $S$-ideles with the $S$-idelic norm $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ (normalized absolute values), $\mu_S=\bigotimes_{v\in S}\mu_v$ the $S$-local multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbb A_{F,S})$, and $\mathcal S(\mathbb A_{F,S})$ the Schwartz–Bruhat space of $\mathbb A_{F,S}$. A *quasi-character* of $\mathrm{GL}_1(\mathbb A_{F,S})$ is a continuous homomorphism $c:\mathrm{GL}_1(\mathbb A_{F,S})\to\mathbb C^\times$; we assume that it has an *exponent* $\sigma\in\mathbb R$, i.e. $|c(g)|=|g|_{F,S}^{\sigma}$ for all $g$. Every quasi-character of $J_{F,S}=\mathrm{GL}_1(\mathbb A_{F,S})/\mathcal O_{F,S}^\times$ (the case of the source) has one, namely its abscissa $\sigma(c)$. For a quasi-character $c$ of exponent $\sigma\in(0,1)$ let $\rho_S(c)$ be the factor of the $S$-local functional equation: the complex number with
--   $$Z_S(f,c)=\rho_S(c)\,Z_S(\widehat f,\widehat c)\qquad\text{for all }f\in\mathcal S(\mathbb A_{F,S}),$$
--   where $Z_S(f,c)=\int f\,c\,d\mu_S$, $\widehat f$ is the $S$-adelic Fourier transform and $\widehat c=|\cdot|_{F,S}\,c^{-1}$ (which has exponent $1-\sigma\in(0,1)$). Let $\bar c$ be the complex conjugate quasi-character and $-1\in\mathrm{GL}_1(\mathbb A_{F,S})$ the $S$-idele with all coordinates $-1$.
--
--   Let $c$ be a quasi-character of exponent $\sigma$ with $0<\sigma<1$. Then:
--
--   1. $Z_S(f,c)=\rho_S(c)\,Z_S(\widehat f,\widehat c)$ for all $f\in\mathcal S(\mathbb A_{F,S})$;
--   2. $\rho_S(c)\,\rho_S(\widehat c)=c(-1)$;
--   3. $\rho_S(\bar c)=c(-1)\,\overline{\rho_S(c)}$;
--   4. if $\sigma=\tfrac12$, then $|\rho_S(c)|=1$.
--
--   These identities control $\rho_S$ on the critical line: by item 4, $\rho_S$ is unimodular on $\sigma(c)=\tfrac12$. In the source they open the study of the correcting factor $\rho_S$ (§3.3.1.1), and item 4 is used in §5.4.2 (p. 274) for the unitarity of the $S$-local Fourier transform.
--
--   **Formalization Note.** A finite set $S\supseteq S_\infty$ of places is represented by the finite set `Sf` of its finite places. $\rho_S(c)$ is `sLocalRho Sf c`, defined as a complex number satisfying item 1 if one exists (and $0$ otherwise); item 1 asserts that it exists, and it is then unique. The source states the identities for the meromorphic function $\rho_S$ on the space $\Omega(J_{F,S})$ of quasi-characters of $J_{F,S}$; here they are stated where $\rho_S$ is defined by the functional equation, i.e. for exponents in $(0,1)$, which determines them everywhere by analytic continuation. The quasi-character is not required to be trivial on the $S$-units.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 132, Proposition 3.3.1.5(1)–(2), eqs. (3.3.1.8)–(3.3.1.9) (proof pp. 132–133); classical reference cited in the proof: J. W. S. Cassels, A. Fröhlich (eds.), Algebraic Number Theory, Ch. XV (J. T. Tate, Fourier analysis in number fields and Hecke's zeta-functions), §2.4, Lemma 2.4.3

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sLocalRho_mul_dual_and_conj
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ)
    (h0 : 0 < σ) (h1 : σ < 1) :
    (∀ f : SAdelicSchwartz F Sf,
      sZetaIntegral f c =
        sLocalRho Sf c * sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf c)) ∧
    sLocalRho Sf c * sLocalRho Sf (sQuasiDual Sf c) = c (-1) ∧
    sLocalRho Sf (fun g => (starRingEnd ℂ) (c g)) =
      c (-1) * (starRingEnd ℂ) (sLocalRho Sf c) ∧
    (σ = 1 / 2 → ‖sLocalRho Sf c‖ = 1) := by sorry

end MasulloGRH
