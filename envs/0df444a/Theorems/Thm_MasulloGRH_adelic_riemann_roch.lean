-- Prove2me | Theorems.Thm_MasulloGRH_adelic_riemann_roch
-- name    : MasulloGRH.adelic_riemann_roch
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T04:32:36.499532+00:00
-- url     : https://prove2.me/theorems/acd22834-7b5b-43fc-aaf9-8f14412ca215
-- title:
--   Theorem 2.2.3.2 — Adelic Riemann–Roch Theorem: $\Phi_F(f)(g)=|g|_F^{-1}\Phi_F(\widehat f)(g^{-1})+|g|_F^{-1}\widehat f(0)-f(0)$
-- statement:
--   This is Tate's Riemann–Roch theorem, the adelic form of the functional equation of the theta function.
--
--   Let $F$ be a number field and $f\in\mathcal S(\mathbb A_F)$ a Schwartz–Bruhat function on the adeles. Let $\widehat f$ be its Fourier transform with respect to the standard additive character and the Tamagawa measure, and
--   $$\Phi_F(f)(g)=\sum_{\xi\in F^\times}f(\xi g)$$
--   its $\theta$-function. Then for every idele $g$ the sums defining $\Phi_F(f)(g)$ and $\Phi_F(\widehat f)(g^{-1})$ converge absolutely, and
--
--   $$\Phi_F(f)(g)=|g|_F^{-1}\,\Phi_F(\widehat f)(g^{-1})+|g|_F^{-1}\,\widehat f(0)-f(0).$$
--
--   The identity exchanges the behaviour of $\Phi_F(f)$ as $|g|_F\to0$ and as $|g|_F\to\infty$, and yields the functional equation of the global zeta integrals.
--
--   **Formalization Note** The statement is for ideles $g$; both sides are invariant under $F^\times$, so it is an identity of functions on $C_F$. Continuity in $g$ is not part of this statement. The convergence of the two sums is stated as unconditional summability over $F^\times$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.2.3.1, Theorem 2.2.3.2 (Adelic Riemann-Roch Theorem), eq. (2.2.3.2), p. 82

import Definitions.Def_MasulloGRH_AdelicTheta

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem adelic_riemann_roch (F : Type*) [Field F] [NumberField F] (f : AdelicSchwartz F)
    (g : IdeleGroup F) :
    Summable (fun ξ : Fˣ =>
      f.eval (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))) ∧
    Summable (fun ξ : Fˣ =>
      adelicFourier f (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g⁻¹ : IdeleGroup F))) ∧
    adelicTheta f g =
      ((ideleNorm g)⁻¹ : ℝ) * adelicThetaFun (adelicFourier f) g⁻¹ +
        ((ideleNorm g)⁻¹ : ℝ) * adelicFourier f 0 - f.eval 0 := by sorry

end MasulloGRH
