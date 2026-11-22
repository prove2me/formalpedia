-- Prove2me | Theorems.Thm_LCAGroup_L1_convolution_commutative_algebra
-- name    : LCAGroup.L1_convolution_commutative_algebra
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:28.720728+00:00
-- url     : https://prove2.me/theorems/0124c84b-0d45-4a57-b9e3-f76e2c881f58
-- title:
--   Eqs. (D.1.1.5)–(D.1.1.6) — $L^1(G)$ is a commutative Banach algebra under convolution: $f*g=g*f$, $(f*g)*h=f*(g*h)$, $\|f*g\|_1\le\|f\|_1\|g\|_1$
-- statement:
--   **The convolution algebra $L^1(G)$ of a locally compact abelian group** (the assertion following (D.1.1.6) in the source: "convolution is a commutative algebra structure on $L^1(G,\mu_G)$").
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$. For $f,g\in L^1(G,\mu_G)$ the convolution
--   $$(f*g)(x)=\int_G f(y)\,g(y^{-1}x)\,d\mu_G(y)\qquad\text{(D.1.1.5)}$$
--   is defined for $\mu_G$-almost every $x$ and is again $\mu_G$-integrable. The theorem states that convolution is a well-defined $\mathbf C$-bilinear multiplication
--   $$*\colon L^1(G,\mu_G)\times L^1(G,\mu_G)\to L^1(G,\mu_G)$$
--   on classes of functions modulo equality almost everywhere, with the following properties for all $f,g,h\in L^1(G,\mu_G)$:
--
--   1. $(f*g)(x)=\int_G f(y)\,g(y^{-1}x)\,d\mu_G(y)$ for $\mu_G$-almost every $x$ (for any choice of representatives);
--   2. commutativity: $f*g=g*f$;
--   3. associativity: $(f*g)*h=f*(g*h)$;
--   4. submultiplicativity of the norm: $\|f*g\|_1\le\|f\|_1\cdot\|g\|_1$ (D.1.1.6).
--
--   Thus $(L^1(G,\mu_G),+,*)$ is a commutative Banach algebra. The Fourier transform $\mathcal F_G\colon L^1(G)\to C_0(\widehat G)$ is a homomorphism for this structure by (D.1.1.12) (platform theorem `LCAGroup.fourier_convolution`), which is the starting point of the Gelfand-theoretic approach to Pontryagin duality and Plancherel's theorem.
--
--   **Formalization Note.** $L^1(G,\mu_G)$ is Mathlib's `Lp ℂ 1 μ`. The statement asserts the existence of a bilinear map `m : Lp ℂ 1 μ →ₗ[ℂ] Lp ℂ 1 μ →ₗ[ℂ] Lp ℂ 1 μ` such that `m f g` is almost everywhere equal to the function `RiemannMasullo.lcaConvolution μ f g` (the platform definition of (D.1.1.5), a Bochner integral, evaluated on the representatives of `f` and `g` chosen by Mathlib); this property determines `m` uniquely, and properties 2–4 are stated for `m`. Haar measures are regular (`IsHaarMeasure` together with `Measure.Regular`), as in the cited reference; no countability assumption is made on $G$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 746, eqs. (D.1.1.5)–(D.1.1.6) and the sentence following (D.1.1.6); classical reference: W. Rudin, Fourier Analysis on Groups, Wiley-Interscience, 1962, Theorem 1.1.6

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology
open scoped ZeroAtInfty

set_option autoImplicit false

namespace LCAGroup

theorem L1_convolution_commutative_algebra
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ m : Lp ℂ 1 μ →ₗ[ℂ] Lp ℂ 1 μ →ₗ[ℂ] Lp ℂ 1 μ,
      (∀ f g : Lp ℂ 1 μ,
        (m f g : G → ℂ) =ᵐ[μ] RiemannMasullo.lcaConvolution μ (f : G → ℂ) (g : G → ℂ)) ∧
      (∀ f g : Lp ℂ 1 μ, m f g = m g f) ∧
      (∀ f g h : Lp ℂ 1 μ, m (m f g) h = m f (m g h)) ∧
      ∀ f g : Lp ℂ 1 μ, ‖m f g‖ ≤ ‖f‖ * ‖g‖ := by sorry

end LCAGroup
