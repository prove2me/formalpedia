-- Prove2me | Theorems.Thm_MasulloGRH_adelicSchwartz_dilation_equiv_and_fourier
-- name    : MasulloGRH.adelicSchwartz_dilation_equiv_and_fourier
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:33.346259+00:00
-- url     : https://prove2.me/theorems/da539536-abd2-450c-8173-6bba472ea43f
-- title:
--   Lemma A.3.1.4 and eqs. (2.2.4.28)–(2.2.4.29) — dilation by an idele $g$ is a topological automorphism of $\mathcal S(\mathbb A_F)$, and $\widehat{f(g\,\cdot)}=|g|_F^{-1}\,\widehat f(g^{-1}\,\cdot)$
-- statement:
--   **Dilations of adelic Schwartz–Bruhat functions and the Fourier transform** (the classical facts behind Lemma 2.2.4.5(3) of the source).
--
--   Let $F$ be a number field, $\mathbb A_F$ its adele ring, $\mathrm{GL}_1(\mathbb A_F)$ its idele group with the idelic norm $|g|_F=\prod_v|g_v|_v$ (the product of the normalized absolute values), $\nu$ the additive Tamagawa measure on $\mathbb A_F$, $\psi$ the standard additive character and $\widehat f(y)=\int_{\mathbb A_F}f(x)\psi(xy)\,d\nu(x)$ the adelic Fourier transform. Let $\mathcal S(\mathbb A_F)$ be the Schwartz–Bruhat space with its locally convex inductive limit topology.
--
--   Let $g\in\mathrm{GL}_1(\mathbb A_F)$ be an idele. Then:
--
--   1. for every $f\in\mathcal S(\mathbb A_F)$ the dilated function $f_g(x)=f(gx)$ is again in $\mathcal S(\mathbb A_F)$, and $f\mapsto f_g$ is a $\mathbb C$-linear homeomorphism of $\mathcal S(\mathbb A_F)$ onto itself;
--   2. the Fourier transform of the dilated function is
--   $$\widehat{f_g}(y)=|g|_F^{-1}\,\widehat f(g^{-1}y)\qquad(y\in\mathbb A_F).$$
--
--   Item 2 is the Fourier-side form of the scaling law $\nu(gB)=|g|_F\,\nu(B)$ of Haar measures on $\mathbb A_F$ (Lemma A.3.1.4 of the source). In the source, item 1 is the action $f\mapsto\rho(g^{-1},f)$, where $\rho(g,f)(x)=f(g^{-1}x)$ is the action of ideles on Schwartz–Bruhat functions (eq. (2.1.2.2) at one place), and item 2 is the identity behind the expressions $|\gamma(t)|_F^{-1}\gamma(t)^*\widehat f$ of (2.2.4.28)–(2.2.4.29), where $\gamma(t)^*u(x)=u(\gamma(t)^{-1}x)$. Applied to Poisson summation it turns $\sum_{\xi\in F}f(\xi)=\sum_{\xi\in F}\widehat f(\xi)$ into the adelic Riemann–Roch theorem $\sum_{\xi\in F}f(g\xi)=|g|_F^{-1}\sum_{\xi\in F}\widehat f(g^{-1}\xi)$.
--
--   **Formalization Note.** The dilation is a continuous linear equivalence `T` of the platform space `MasulloGRH.AdelicSchwartz F` with `(T f).eval x = f.eval (g * x)`; the second item is stated for the function `MasulloGRH.adelicFourier (T f)`. The source uses these facts without a numbered statement; they are stated here for an arbitrary idele $g$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 92, Lemma 2.2.4.5(3), eqs. (2.2.4.28)–(2.2.4.29) (the functions $|\gamma(t)|_F^{-1}\gamma(t)^*\widehat f$), with p. 93, eqs. (2.2.4.34)–(2.2.4.35), p. 65, eq. (2.1.2.2) (the dilation action), and p. 556, Lemma A.3.1.4, eq. (A.3.1.4); classical reference cited at Lemma A.3.1.4: J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, Lemma 4.1.2

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem adelicSchwartz_dilation_equiv_and_fourier
    (F : Type*) [Field F] [NumberField F] (g : IdeleGroup F) :
    ∃ T : AdelicSchwartz F ≃L[ℂ] AdelicSchwartz F,
      (∀ (f : AdelicSchwartz F) (x : AdeleRing (𝓞 F) F),
        (T f).eval x = f.eval ((g : AdeleRing (𝓞 F) F) * x)) ∧
      ∀ (f : AdelicSchwartz F) (y : AdeleRing (𝓞 F) F),
        adelicFourier (T f) y =
          (((ideleNorm g)⁻¹ : ℝ) : ℂ) *
            adelicFourier f (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) * y) := by sorry

end MasulloGRH
