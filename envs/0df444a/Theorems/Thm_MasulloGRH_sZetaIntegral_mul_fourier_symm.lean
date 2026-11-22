-- Prove2me | Theorems.Thm_MasulloGRH_sZetaIntegral_mul_fourier_symm
-- name    : MasulloGRH.sZetaIntegral_mul_fourier_symm
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:29:41.660795+00:00
-- url     : https://prove2.me/theorems/1d135842-6f5a-4f70-bd7a-959945790fb1
-- title:
--   Tate's symmetry lemma for $S$-local zeta integrals: $Z_S(f,c)\,Z_S(\widehat h,\widehat c)=Z_S(h,c)\,Z_S(\widehat f,\widehat c)$ for $0<\sigma(c)<1$
-- statement:
--   **Tate's symmetry lemma for the $S$-local zeta integrals:** $Z_S(f,c)\,Z_S(\widehat h,\widehat c)=Z_S(h,c)\,Z_S(\widehat f,\widehat c)$ for every quasi-character $c$ of exponent in $(0,1)$ (the $S$-local form of the symmetry lemma in §2.4 of Tate's thesis).
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$ be the ring of $S$-adeles, $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ the group of $S$-ideles with the $S$-idelic norm $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ (normalized absolute values), $\nu_S$ the $S$-local additive Tamagawa measure on $\mathbb A_{F,S}$, $\mu_S$ the $S$-local multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbb A_{F,S})$, $\psi_{S,\mathrm{std}}$ the standard additive character and $\mathcal S(\mathbb A_{F,S})$ the Schwartz–Bruhat space. For $f\in\mathcal S(\mathbb A_{F,S})$ let
--   $$\widehat f(y)=\int_{\mathbb A_{F,S}}f(x)\,\psi_{S,\mathrm{std}}(xy)\,d\nu_S(x)$$
--   be its $S$-adelic Fourier transform, and for a function $\varphi$ on $\mathbb A_{F,S}$ and a function $c$ on $\mathrm{GL}_1(\mathbb A_{F,S})$ put
--   $$Z_S(\varphi,c)=\int_{\mathrm{GL}_1(\mathbb A_{F,S})}\varphi(g)\,c(g)\,d\mu_S(g).$$
--
--   Let $c\colon\mathrm{GL}_1(\mathbb A_{F,S})\to\mathbb C^\times$ be a quasi-character (a continuous homomorphism) of exponent $\sigma$, i.e. $|c(g)|=|g|_{F,S}^{\sigma}$ for all $g$, with
--   $$0<\sigma<1,$$
--   and let $\widehat c=|\cdot|_{F,S}\,c^{-1}$ be the dual quasi-character, of exponent $1-\sigma$. Then for all $f,h\in\mathcal S(\mathbb A_{F,S})$
--   $$Z_S(f,c)\,Z_S(\widehat h,\widehat c)=Z_S(h,c)\,Z_S(\widehat f,\widehat c).$$
--
--   This is the key step of Tate's proof of the local functional equation (Cassels–Fröhlich, Ch. XV, §2.4, proof of Theorem 2.4.1), carried out on the locally compact ring $\mathbb A_{F,S}$ instead of a single completion. The source proves Theorem 3.3.1.1(1)(a) (p. 131) by reducing to pure tensors and applying Tate's local functional equation (Cassels–Fröhlich, Ch. XV, Theorem 2.4.1) at each place of $S$, which rests on the local form of this lemma; the present statement is its direct $S$-local form. Together with the existence of one $f$ with $Z_S(\widehat f,\widehat c)\neq0$ it shows that the ratio $Z_S(f,c)/Z_S(\widehat f,\widehat c)$ does not depend on $f$, which is the factor $\rho_S(c)$ of the $S$-local functional equation.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. The quasi-character is not required to be trivial on the $S$-units. The exponent hypothesis is `‖c g‖ = sIdeleNorm Sf g ^ σ`; $\widehat c$ is `MasulloGRH.sQuasiDual Sf c`, $\widehat f$ is `MasulloGRH.sLocalFourier Sf f.eval`, and $Z_S$ is `MasulloGRH.sZetaIntegral` / `MasulloGRH.sZetaIntegralFun` (Bochner integrals). For $0<\sigma<1$ all four integrals converge absolutely (the exponents of $c$ and $\widehat c$ are $\sigma>0$ and $1-\sigma>0$); the formal statement asserts only the identity.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 131, proof of Theorem 3.3.1.1(1)(a) (auxiliary lemma for the proof of Theorem 3.3.1.1(1)(a)–(b), MasulloGRH.sZetaIntegral_functional_equation_and_continuation); classical reference: J. T. Tate, Fourier analysis in number fields and Hecke's zeta-functions, in J. W. S. Cassels, A. Fröhlich (eds.), Algebraic Number Theory, Ch. XV, §2.4 (the symmetry lemma in the proof of Theorem 2.4.1)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sZetaIntegral_mul_fourier_symm
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ)
    (h0 : 0 < σ) (h1 : σ < 1) (f h : SAdelicSchwartz F Sf) :
    sZetaIntegral f c * sZetaIntegralFun Sf (sLocalFourier Sf h.eval) (sQuasiDual Sf c) =
      sZetaIntegral h c * sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf c) := by sorry

end MasulloGRH
