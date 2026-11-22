-- Prove2me | Theorems.Thm_LCAGroup_fourier_L1_to_zeroAtInfty_injective
-- name    : LCAGroup.fourier_L1_to_zeroAtInfty_injective
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:37.644803+00:00
-- url     : https://prove2.me/theorems/14d0fb93-ad62-40bc-845c-5284108af968
-- title:
--   Lemma D.1.1.2(1)–(2) — the Fourier transform $\mathcal F_G\colon L^1(G)\to C_0(\widehat G)$ is linear, injective and satisfies $\|\widehat f\|_u\le\|f\|_1$
-- statement:
--   **Riemann–Lebesgue lemma and uniqueness theorem for the Fourier transform on a locally compact abelian group** (Lemma D.1.1.2(1)–(2) of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu$, and let $\widehat G$ be its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). The Fourier transform of $f\in L^1(G,\mu)$ is the function on $\widehat G$
--   $$\widehat f(\chi)=\int_G f(x)\,\overline{\chi(x)}\,d\mu(x).$$
--   Then:
--
--   1. for every $f\in L^1(G,\mu)$ the function $\widehat f$ is continuous and vanishes at infinity, $\widehat f\in C_0(\widehat G)$;
--   2. $f\mapsto\widehat f$ is a $\mathbb C$-linear map $\mathcal F_G\colon L^1(G,\mu)\to C_0(\widehat G)$ which is **injective** and satisfies
--   $$\|\widehat f\|_u\le\|f\|_1 ,$$
--   where $\|\cdot\|_u$ is the supremum norm on $C_0(\widehat G)$; in particular $\mathcal F_G$ is continuous.
--
--   Injectivity is the uniqueness theorem: an integrable function is determined almost everywhere by its Fourier transform. Together with the convolution theorem this makes $\mathcal F_G$ an injective, norm-decreasing homomorphism from the Banach algebra $L^1(G)$ to $C_0(\widehat G)$. The source collects these facts for use with $G=\mathbb A_F$, $F_v$, $F_v^\times$, $C_F$ and their Schwartz–Bruhat spaces.
--
--   **Formalization Note.** The statement asserts the existence of a linear map `F : Lp ℂ 1 μ →ₗ[ℂ] C₀(PontryaginDual G, ℂ)` whose value at a class $f$ is the function $\chi\mapsto$ `RiemannMasullo.lcaFourier μ f χ` $=\int f(x)\overline{\chi(x)}\,d\mu(x)$ (platform definition `RiemannMasullo_LCAFourierConvolution`), together with `Function.Injective F` and `‖F f‖ ≤ ‖f‖`. The integral depends only on the almost-everywhere class of $f$, so for an integrable function $f$ the function $\widehat f$ is the element $F[f]$ of $C_0(\widehat G)$. Haar measures are regular (`IsHaarMeasure` together with Mathlib's `Measure.Regular`), i.e. Haar measures in the classical Radon sense of the cited references; regularity is automatic when $G$ is second countable. $G$ carries its Borel $\sigma$-algebra (`[BorelSpace G]`), and groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 746–747, Lemma D.1.1.2(1)–(2), eqs. (D.1.1.4), (D.1.1.7); classical reference: W. Rudin, Fourier Analysis on Groups, Wiley-Interscience, 1962, Theorem 1.2.4(a, d); A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Corollary 3.3.4 (injectivity)

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology
open scoped ZeroAtInfty

set_option autoImplicit false

namespace LCAGroup

theorem fourier_L1_to_zeroAtInfty_injective
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ F : Lp ℂ 1 μ →ₗ[ℂ] C₀(PontryaginDual G, ℂ),
      (∀ (f : Lp ℂ 1 μ) (χ : PontryaginDual G),
        F f χ = RiemannMasullo.lcaFourier μ (f : G → ℂ) χ) ∧
      Function.Injective F ∧
      ∀ f : Lp ℂ 1 μ, ‖F f‖ ≤ ‖f‖ := by sorry

end LCAGroup
