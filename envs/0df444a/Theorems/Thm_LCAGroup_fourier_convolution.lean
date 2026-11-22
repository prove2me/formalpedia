-- Prove2me | Theorems.Thm_LCAGroup_fourier_convolution
-- name    : LCAGroup.fourier_convolution
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:41.084028+00:00
-- url     : https://prove2.me/theorems/b396e045-3f55-44ec-80cb-ab72ae07faf2
-- title:
--   Eqs. (D.1.1.5)–(D.1.1.6) and Lemma D.1.1.2(6) — convolution on $L^1(G)$: $\|f_1*f_2\|_1\le\|f_1\|_1\|f_2\|_1$ and $\mathcal F_G(f_1*f_2)=\mathcal F_G(f_1)\cdot\mathcal F_G(f_2)$
-- statement:
--   **Convolution theorem for the Fourier transform on a locally compact abelian group** (eqs. (D.1.1.5)–(D.1.1.6) and Lemma D.1.1.2(6) of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu$ and Pontryagin dual $\widehat G$, and let $f_1,f_2\in L^1(G,\mu)$. Their convolution is
--   $$(f_1*f_2)(x)=\int_G f_1(y)\,f_2(y^{-1}x)\,d\mu(y),$$
--   and the Fourier transform of $f\in L^1(G,\mu)$ is $\widehat f(\chi)=\int_G f(x)\overline{\chi(x)}\,d\mu(x)$ for $\chi\in\widehat G$. Then:
--
--   1. for $\mu$-almost every $x\in G$ the function $y\mapsto f_1(y)f_2(y^{-1}x)$ is $\mu$-integrable, so $(f_1*f_2)(x)$ is defined almost everywhere;
--   2. $f_1*f_2$ is $\mu$-integrable and
--   $$\|f_1*f_2\|_1\le\|f_1\|_1\cdot\|f_2\|_1 ;$$
--   3. for every $\chi\in\widehat G$,
--   $$\widehat{f_1*f_2}(\chi)=\widehat{f_1}(\chi)\cdot\widehat{f_2}(\chi).$$
--
--   Thus $L^1(G,\mu)$ is a Banach algebra under convolution and the Fourier transform $\mathcal F_G\colon L^1(G)\to C_0(\widehat G)$ is an algebra homomorphism to pointwise multiplication. The source recalls this among the basic properties of the Fourier transform used for the adelic and idelic groups of Appendix D.
--
--   **Formalization Note.** `RiemannMasullo.lcaConvolution μ f g x` and `RiemannMasullo.lcaFourier μ f χ` are the Bochner integrals $\int f(y)g(y^{-1}x)\,d\mu(y)$ and $\int f(x)\overline{\chi(x)}\,d\mu(x)$ of the platform definition `RiemannMasullo_LCAFourierConvolution`. A Bochner integral is $0$ by convention when the integrand is not integrable; part 1 records that for the convolution this happens only on a $\mu$-null set of $x$, and part 2 asserts integrability of the resulting function, so that the transform in part 3 is a genuine integral. The $L^1$-norms in part 2 are written as $\int\|\cdot\|\,d\mu$. Haar measures are regular (`IsHaarMeasure` together with Mathlib's `Measure.Regular`), i.e. Haar measures in the classical Radon sense of the cited references; regularity is automatic when $G$ is second countable. $G$ carries its Borel $\sigma$-algebra (`[BorelSpace G]`), and groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 746–747, eqs. (D.1.1.5)–(D.1.1.6) and Lemma D.1.1.2(6), eq. (D.1.1.12); classical reference: W. Rudin, Fourier Analysis on Groups, Wiley-Interscience, 1962, Theorem 1.1.6 and Theorem 1.2.4(b)

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology
open scoped ZeroAtInfty

set_option autoImplicit false

namespace LCAGroup

theorem fourier_convolution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (f g : G → ℂ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ᵐ x ∂μ, Integrable (fun y : G => f y * g (y⁻¹ * x)) μ) ∧
    Integrable (RiemannMasullo.lcaConvolution μ f g) μ ∧
    (∫ x, ‖RiemannMasullo.lcaConvolution μ f g x‖ ∂μ ≤ (∫ x, ‖f x‖ ∂μ) * ∫ x, ‖g x‖ ∂μ) ∧
    ∀ χ : PontryaginDual G,
      RiemannMasullo.lcaFourier μ (RiemannMasullo.lcaConvolution μ f g) χ =
        RiemannMasullo.lcaFourier μ f χ * RiemannMasullo.lcaFourier μ g χ := by sorry

end LCAGroup
