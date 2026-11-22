-- Prove2me | Theorems.Thm_LCAGroup_weil_integrable_of_iterated_lintegral_lt_top
-- name    : LCAGroup.weil_integrable_of_iterated_lintegral_lt_top
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:21.003806+00:00
-- url     : https://prove2.me/theorems/4f3423da-cf28-488f-a75a-00495af78da4
-- title:
--   Lemma D.1.2.3 — converse to Weil's formula for $\sigma$-finite $G$: if $\int_{G/H}\int_H|f(xh)|\,d\mu_H(h)\,d\nu(x)<\infty$ then $f\in L^1(G)$ and Weil's formula holds
-- statement:
--   **Integrability criterion via the iterated integral over $G/H$ and $H$** (Lemma D.1.2.3 of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group, $H\subseteq G$ a closed subgroup, and let $\mu_G$, $\mu_H$ be Haar measures on $G$ and $H$. Let $\nu$ be the quotient Haar measure on $G/H$ of Theorem D.1.2.1, i.e. the Haar measure on $G/H$ for which
--   $$\int_G \varphi(g)\,d\mu_G(g)=\int_{G/H}\int_H \varphi(xh)\,d\mu_H(h)\,d\nu(x)\qquad\text{for all }\varphi\in C_c(G).$$
--   Assume that $G$ is $\sigma$-finite (for $\mu_G$), and let $f\colon G\to\mathbf C$ be a measurable function such that the iterated integral
--   $$\int_{G/H}\int_H |f(xh)|\,d\mu_H(h)\,d\nu(x)\qquad\text{(D.1.2.2)}$$
--   is finite. Then $f$ is $\mu_G$-integrable, and Weil's formula holds for $f$:
--   $$\int_G f(g)\,d\mu_G(g)=\int_{G/H}\int_H f(xh)\,d\mu_H(h)\,d\nu(x).$$
--
--   This is the Tonelli-type companion of the $L^1$ statement of Theorem D.1.2.1 (platform theorem `LCAGroup.weil_quotient_integral_formula`): it allows one to *prove* integrability on $G$ by estimating first along the cosets of $H$ and then on the quotient, as one does for the adelic quotients $\mathbb A_F/F$ and $\mathrm{GL}_1(\mathbb A_F)/F^\times$. The $\sigma$-finiteness hypothesis cannot be dropped: for $G=\mathbb R\times\mathbb R_{\mathrm d}$ (with $\mathbb R_{\mathrm d}$ the discrete reals), $H=\mathbb R\times\{0\}$ and $f$ the indicator function of the closed subgroup $\{0\}\times\mathbb R_{\mathrm d}$, every inner integral vanishes, while $f$ is not integrable for the (regular) Haar measure.
--
--   **Formalization Note.** $\sigma$-finiteness is `SigmaFinite μ`; measurability of $f$ is `AEStronglyMeasurable f μ` (measurability with respect to the completion of $\mu_G$; in particular every Borel measurable $f$ is allowed). The iterated integral (D.1.2.2) is the lower Lebesgue integral `∫⁻ q, (∫⁻ h : H, ‖f (q.out * h)‖ₑ ∂μH) ∂ν` with values in $[0,\infty]$, computed at the representative `q.out` of the coset `q` (the inner integral does not depend on the representative, by invariance of $\mu_H$), and "converges" means that it is `< ⊤`. `ν` is a regular Haar measure on `G ⧸ H` satisfying the hypothesis `hν` (Weil's formula on $C_c(G)$), which determines it; in the conclusion the integrals are Bochner integrals, as in `LCAGroup.weil_quotient_integral_formula`. Haar measures are regular (`IsHaarMeasure` together with `Measure.Regular`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 747–748, Lemma D.1.2.3, eq. (D.1.2.2); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Corollary 1.5.4

import Mathlib

open MeasureTheory Topology

set_option autoImplicit false

namespace LCAGroup

theorem weil_integrable_of_iterated_lintegral_lt_top
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite μ]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    (f : G → ℂ) (hf : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ q : G ⧸ H, (∫⁻ h : H, ‖f (q.out * (h : G))‖ₑ ∂μH) ∂ν < ⊤) :
    Integrable f μ ∧
    ∫ x, f x ∂μ = ∫ q : G ⧸ H, (∫ h : H, f (q.out * (h : G)) ∂μH) ∂ν := by sorry

end LCAGroup
