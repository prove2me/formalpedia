-- Prove2me | Theorems.Thm_LCAGroup_poisson_summation
-- name    : LCAGroup.poisson_summation
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:51:05.932211+00:00
-- url     : https://prove2.me/theorems/403032d7-26c6-4504-8f09-df263978bf42
-- title:
--   Theorem D.1.2.7 — Poisson summation formula for a closed subgroup $H$ of a locally compact abelian group: $\int_H f(xh)\,d\mu_H=\int_{H^\perp}\widehat f(\chi)\chi(x)\,d\mu_{H^\perp}$
-- statement:
--   **Poisson summation formula for a closed subgroup of a locally compact abelian group** (Situation D.1.2.6 and Theorem D.1.2.7 of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group, $H\subseteq G$ a closed subgroup and $\pi\colon G\to G/H$ the quotient map. Fix Haar measures $\mu_G$ on $G$ and $\mu_H$ on $H$; let $\mu_{G/H}$ be the quotient Haar measure on $G/H$ determined by Weil's formula $\int_G\varphi\,d\mu_G=\int_{G/H}\int_H\varphi(xh)\,d\mu_H(h)\,d\mu_{G/H}(x)$ for $\varphi\in C_c(G)$, and let $\mu_{\widehat{G/H}}$ be the Plancherel measure of $\mu_{G/H}$ on the dual group $\widehat{G/H}$. The map $\eta\mapsto\eta\circ\pi$ identifies $\widehat{G/H}$ with the annihilator $H^\perp=\{\chi\in\widehat G:\chi(H)=1\}$, and $\mu_{H^\perp}$ denotes the Haar measure on $H^\perp$ corresponding to $\mu_{\widehat{G/H}}$.
--
--   Let $f\in L^1(G,\mu_G)$, with Fourier transform $\widehat f(\chi)=\int_G f(x)\overline{\chi(x)}\,d\mu_G(x)$, and let
--   $$f^H(x)=\int_H f(xh)\,d\mu_H(h),$$
--   which is defined for almost all cosets $xH$ and is $\mu_{G/H}$-integrable on $G/H$. Then:
--
--   1. $\widehat{f^H}(\eta)=\widehat f(\eta\circ\pi)$ for every $\eta\in\widehat{G/H}$: under $\widehat{G/H}\cong H^\perp$ the Fourier transform of $f^H$ is the restriction $\widehat f|_{H^\perp}$.
--   2. If $\widehat f|_{H^\perp}$ is $\mu_{H^\perp}$-integrable, then the Poisson summation formula
--   $$\int_H f(xh)\,d\mu_H(h)=\int_{H^\perp}\widehat f(\chi)\,\chi(x)\,d\mu_{H^\perp}(\chi)$$
--   holds for $\mu_{G/H}$-almost every coset $xH$.
--   3. If moreover the integral $f^H(x)$ exists for every $x\in G$ and $f^H$ is continuous on $G$, then the formula holds for **every** $x\in G$.
--
--   For $G=\mathbb R$, $H=\mathbb Z$ with Lebesgue and counting measure this is the classical formula $\sum_{n\in\mathbb Z}f(x+n)=\sum_{k\in\mathbb Z}\widehat f(k)e^{2\pi i kx}$. The source records the general form for use with $F\subset\mathbb A_F$ and its $S$-adic and idelic variants (functional equations of theta functions and zeta integrals).
--
--   **Deviation from the source.** (i) In part 2 the source says "for $\mu_G$-almost all $x\in G$". Both sides depend only on the coset $xH$, and the exceptional set is here a $\mu_{G/H}$-null set of cosets. The two formulations agree when $G$ is $\sigma$-compact (in particular second countable); for general $G$ the preimage in $G$ of a null set of cosets need not be $\mu_G$-null, so the quotient formulation is the one that holds in general. (ii) The source prints the left-hand side as $\int_H f(h^{-1}x)\,d\mu_H(h)$; it equals $\int_H f(xh)\,d\mu_H(h)$ because $G$ is abelian and $\mu_H$ is invariant under inversion.
--
--   **Formalization Note.** Instead of transporting the measure to the subgroup $H^\perp\subseteq\widehat G$, the right-hand side is an integral over `PontryaginDual (G ⧸ H)` against a measure `ν'` with `LCAGroup.IsPlancherelMeasure ν ν'`, and $\widehat f(\eta\circ\pi)$ is written out as $\int_G f(x)\,\overline{\eta(xH)}\,d\mu$ (here `(x : G ⧸ H)` is the coset of `x`). `ν` is a regular Haar measure on `G ⧸ H` satisfying Weil's formula on $C_c(G)$ (hypothesis `hν`), which determines it uniquely. In parts 1 and 2 the function $f^H$ on `G ⧸ H` is `q ↦ ∫ h : H, f (q.out * h) ∂μH` (representative `q.out`); in part 3 it is the function `y ↦ ∫ h : H, f (y * h) ∂μH` on $G$, with integrability of every fibre as a hypothesis, as in the source. Bochner integrals are $0$ when the integrand is not integrable. The Borel $\sigma$-algebras on `G ⧸ H` and on `PontryaginDual (G ⧸ H)` enter through typeclass binders. Haar measures are regular (`IsHaarMeasure` together with Mathlib's `Measure.Regular`), i.e. Haar measures in the classical Radon sense of the cited references; regularity is automatic when $G$ is second countable. $G$ carries its Borel $\sigma$-algebra (`[BorelSpace G]`), and groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 748–749, Situation D.1.2.6 and Theorem D.1.2.7, eqs. (D.1.2.7)–(D.1.2.8); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Theorem 3.6.3

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_PlancherelMeasure

open MeasureTheory Topology

set_option autoImplicit false

namespace LCAGroup

theorem poisson_summation
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    [MeasurableSpace (PontryaginDual (G ⧸ H))] [BorelSpace (PontryaginDual (G ⧸ H))]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    (ν' : Measure (PontryaginDual (G ⧸ H))) (hν' : IsPlancherelMeasure ν ν')
    (f : G → ℂ) (hf : Integrable f μ) :
    (∀ η : PontryaginDual (G ⧸ H),
      RiemannMasullo.lcaFourier ν (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) η =
        ∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) ∧
    (Integrable (fun η : PontryaginDual (G ⧸ H) =>
        ∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) ν' →
      (∀ᵐ q ∂ν, ∫ h : H, f (q.out * (h : G)) ∂μH =
        ∫ η : PontryaginDual (G ⧸ H),
          (∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) * (η q : ℂ) ∂ν') ∧
      ((∀ y : G, Integrable (fun h : H => f (y * (h : G))) μH) →
        Continuous (fun y : G => ∫ h : H, f (y * (h : G)) ∂μH) →
        ∀ y : G, ∫ h : H, f (y * (h : G)) ∂μH =
          ∫ η : PontryaginDual (G ⧸ H),
            (∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) * (η (y : G ⧸ H) : ℂ) ∂ν')) := by sorry

end LCAGroup
