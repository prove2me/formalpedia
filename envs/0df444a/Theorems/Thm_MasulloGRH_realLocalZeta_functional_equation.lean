-- Prove2me | Theorems.Thm_MasulloGRH_realLocalZeta_functional_equation
-- name    : MasulloGRH.realLocalZeta_functional_equation
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:26.063061+00:00
-- url     : https://prove2.me/theorems/061cc1d0-df7b-47aa-83e3-2ef195f82141
-- title:
--   Eqs. (3.3.2.12)–(3.3.2.13) — Tate's local functional equation at a real place, with $\rho(|\cdot|^s)=\Gamma_{\mathbb R}(s)/\Gamma_{\mathbb R}(1-s)$ and the factor $i$ on the sign component
-- statement:
--   **The local functional equation at a real place, with its explicit factor** (eqs. (3.3.2.11)–(3.3.2.13) of the source, recalled from Tate's thesis).
--
--   Let $f\in\mathcal S(\mathbb R)$ be a Schwartz function and
--   $$\widehat f(\xi)=\int_{\mathbb R}f(x)\,e^{-2\pi i x\xi}\,dx$$
--   its Fourier transform. For a quasi-character $c$ of $\mathbb R^\times$ the local zeta integral is $Z(f,c)=\int_{\mathbb R^\times}f(x)\,c(x)\,\frac{dx}{|x|}$, and $\widehat c=|\cdot|\,c^{-1}$. Write $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$. Then for every $s\in\mathbb C$ with $0<\operatorname{Re}s<1$:
--
--   1. (trivial component, $c=|\cdot|^s$, $\widehat c=|\cdot|^{1-s}$)
--   $$\Gamma_{\mathbb R}(1-s)\int_{\mathbb R}f(x)\,|x|^{s-1}\,dx=\Gamma_{\mathbb R}(s)\int_{\mathbb R}\widehat f(x)\,|x|^{-s}\,dx;$$
--   2. (sign component, $c=\mathrm{sgn}\,|\cdot|^s$, $\widehat c=\mathrm{sgn}\,|\cdot|^{1-s}$)
--   $$\Gamma_{\mathbb R}(2-s)\int_{\mathbb R}f(x)\,\mathrm{sgn}(x)\,|x|^{s-1}\,dx=i\,\Gamma_{\mathbb R}(s+1)\int_{\mathbb R}\widehat f(x)\,\mathrm{sgn}(x)\,|x|^{-s}\,dx.$$
--
--   Equivalently $Z(f,c)=\rho(c)\,Z(\widehat f,\widehat c)$ with
--   $$\rho(|\cdot|^s)=\frac{\pi^{-s/2}\Gamma(\frac s2)}{\pi^{-(1-s)/2}\Gamma(\frac{1-s}2)},\qquad\rho(\mathrm{sgn}\,|\cdot|^s)=i\,\frac{\pi^{-(s+1)/2}\Gamma(\frac{s+1}2)}{\pi^{-((1-s)+1)/2}\Gamma(\frac{(1-s)+1}2)},$$
--   which are (3.3.2.12) and the first expression in (3.3.2.13). All four integrals converge absolutely in the strip. These are the archimedean factors $\rho_v$ of the $S$-local functional equation at the real places; their poles give the poles of the local $Z$-functions (Lemma 3.3.2.1), and their size on vertical lines is what the source estimates in §3.3.1.1.
--
--   **Deviation from the source.** The second expression in (3.3.2.13), $-i\,2^{1-s}\pi^{-s}\sin(\frac{\pi s}2)\Gamma(s)$, has the wrong sign: with the kernel $e^{-2\pi ix\xi}$ of the source, $\rho(\mathrm{sgn}\,|\cdot|^s)=+i\,2^{1-s}\pi^{-s}\sin(\frac{\pi s}2)\Gamma(s)$ (check: $f(x)=xe^{-\pi x^2}$ has $\widehat f(\xi)=-i\,\xi e^{-\pi\xi^2}$).
--
--   **Formalization Note.** The Fourier transform is Mathlib's `𝓕` on `SchwartzMap ℝ ℂ`, with kernel $e^{-2\pi ix\xi}$; this is the transform attached to the real component $x\mapsto e^{-2\pi ix}$ of the standard additive character in the platform's conventions (`MasulloGRH.sStdCharacter`), and the self-dual measure is Lebesgue measure. With the opposite sign of the character the factor $i$ in item 2 becomes $-i$. The integrals over $\mathbb R^\times$ against $dx/|x|$ are written as integrals over $\mathbb R$ of $f(x)|x|^{s-1}$; $\Gamma_{\mathbb R}$ is `Complex.Gammaℝ`. The identities are cross-multiplied to avoid division.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 139, eqs. (3.3.2.11)–(3.3.2.13) (proof of Lemma 3.3.2.1); classical references cited there: J. W. S. Cassels, A. Fröhlich (eds.), Algebraic Number Theory, Ch. XV (J. T. Tate, Fourier analysis in number fields and Hecke's zeta-functions), Theorem 2.4.1 and §2.5

import Mathlib

open MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace MasulloGRH

theorem realLocalZeta_functional_equation
    (f : SchwartzMap ℝ ℂ) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    (∫ x : ℝ, f x * ((|x| : ℝ) : ℂ) ^ (s - 1)) * Complex.Gammaℝ (1 - s) =
      Complex.Gammaℝ s * ∫ x : ℝ, (𝓕 f) x * ((|x| : ℝ) : ℂ) ^ (-s) ∧
    (∫ x : ℝ, f x * ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)) * Complex.Gammaℝ (2 - s) =
      Complex.I * Complex.Gammaℝ (s + 1) *
        ∫ x : ℝ, (𝓕 f) x * ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (-s) := by sorry

end MasulloGRH
