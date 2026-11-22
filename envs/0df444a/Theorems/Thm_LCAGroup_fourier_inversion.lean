-- Prove2me | Theorems.Thm_LCAGroup_fourier_inversion
-- name    : LCAGroup.fourier_inversion
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:56.575184+00:00
-- url     : https://prove2.me/theorems/53b324d7-e29d-4fb0-a0d8-141ffb5c0703
-- title:
--   Lemma D.1.1.2(5), corrected — Fourier inversion on a locally compact abelian group: $f(x)=\int_{\widehat G}\widehat f(\chi)\,\chi(x)\,d\mu_{\widehat G}(\chi)$
-- statement:
--   **Fourier inversion theorem for locally compact abelian groups** (Lemma D.1.1.2(5) of the source, in its correct classical form).
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$, let $\widehat G$ be its Pontryagin dual, and let $\mu_{\widehat G}$ be the Plancherel measure of $\mu_G$ on $\widehat G$ (the unique Haar measure on $\widehat G$ with $\|\widehat f\|_2=\|f\|_2$ for $f\in L^1\cap L^2$). Let $f\in L^1(G,\mu_G)$ be such that its Fourier transform $\widehat f(\chi)=\int_G f(x)\overline{\chi(x)}\,d\mu_G(x)$ is integrable, $\widehat f\in L^1(\widehat G,\mu_{\widehat G})$. Then the inversion formula
--   $$f(x)=\int_{\widehat G}\widehat f(\chi)\,\chi(x)\,d\mu_{\widehat G}(\chi)$$
--   holds
--
--   1. for $\mu_G$-almost every $x\in G$, and
--   2. for **every** $x\in G$ if $f$ is continuous.
--
--   Under the Pontryagin isomorphism $\iota_G\colon G\cong\widehat{\widehat G}$ the right-hand side is $\mathcal F_{\widehat G}(\mathcal F_G(f))$ evaluated at $\iota_G(x^{-1})$, so the formula is $f(x^{-1})=\mathcal F_{\widehat G}(\mathcal F_G(f))(x)$, eq. (D.1.1.11) of the source. The right-hand side is a continuous function of $x$, so part 1 says that $f$ agrees almost everywhere with a continuous function. Inversion is what makes the Fourier transform an isomorphism on Schwartz–Bruhat spaces, and it is the analytic input of the Poisson summation formula (Theorem D.1.2.7).
--
--   **Deviation from the source.** The source asserts that $f$ itself is continuous and that the formula holds at every point. For an arbitrary integrable function this is false: the indicator function of a point of $\mathbb R$ has $\widehat f=0$ but is not $0$ at that point. The classical theorem, stated here, gives the formula almost everywhere, and everywhere for continuous $f$.
--
--   **Formalization Note.** `ν` is any measure on `PontryaginDual G` with `LCAGroup.IsPlancherelMeasure μ ν` (definition `LCAGroup_PlancherelMeasure`; by the Plancherel theorem there is exactly one). The hypotheses are `Integrable f μ` and `Integrable (RiemannMasullo.lcaFourier μ f) ν`; the conclusion is the conjunction of the almost-everywhere statement and of `Continuous f → ∀ x, …`. The character value $\chi(x)\in$ `Circle` is coerced to $\mathbb C$. Haar measures are regular (`IsHaarMeasure` together with Mathlib's `Measure.Regular`), i.e. Haar measures in the classical Radon sense of the cited references; regularity is automatic when $G$ is second countable. $G$ carries its Borel $\sigma$-algebra (`[BorelSpace G]`), and groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 747, Lemma D.1.1.2(5), eq. (D.1.1.11); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Theorem 3.5.8

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_PlancherelMeasure

open MeasureTheory Topology

set_option autoImplicit false

namespace LCAGroup

theorem fourier_inversion
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (ν : Measure (PontryaginDual G)) (hν : IsPlancherelMeasure μ ν)
    (f : G → ℂ) (hf : Integrable f μ)
    (hf' : Integrable (RiemannMasullo.lcaFourier μ f) ν) :
    (∀ᵐ x ∂μ, f x = ∫ χ : PontryaginDual G, RiemannMasullo.lcaFourier μ f χ * (χ x : ℂ) ∂ν) ∧
    (Continuous f →
      ∀ x : G, f x = ∫ χ : PontryaginDual G, RiemannMasullo.lcaFourier μ f χ * (χ x : ℂ) ∂ν) := by sorry

end LCAGroup
