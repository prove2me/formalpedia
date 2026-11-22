-- Prove2me | Theorems.Thm_LCAGroup_weil_quotient_integral_formula
-- name    : LCAGroup.weil_quotient_integral_formula
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:29.274818+00:00
-- url     : https://prove2.me/theorems/35438454-1f06-4343-b445-5e80f36bdc8e
-- title:
--   Theorem D.1.2.1 — Weil's quotient integral formula $\int_G f\,d\mu_G=\int_{G/H}\int_H f(xh)\,d\mu_H(h)\,d\nu(x)$ for $f\in L^1(G)$
-- statement:
--   **Weil's quotient integral formula for integrable functions** (Theorem D.1.2.1 of the source, final assertion).
--
--   Let $G$ be a Hausdorff locally compact abelian group, $H\subseteq G$ a closed subgroup, and let $\mu_G$, $\mu_H$ be Haar measures on $G$ and $H$. Let $\nu$ be the quotient Haar measure on $G/H$ determined by $\mu_G$ and $\mu_H$, i.e. the Haar measure on $G/H$ for which
--   $$\int_G \varphi(g)\,d\mu_G(g)=\int_{G/H}\int_H \varphi(xh)\,d\mu_H(h)\,d\nu(x)\qquad\text{for all }\varphi\in C_c(G).$$
--   Then for every $f\in L^1(G,\mu_G)$:
--
--   1. for $\nu$-almost every coset $xH\in G/H$ the function $h\mapsto f(xh)$ is $\mu_H$-integrable on $H$;
--   2. the function $f^H(xH)=\int_H f(xh)\,d\mu_H(h)$, defined for almost all cosets, is $\nu$-integrable on $G/H$;
--   3. Weil's formula holds for $f$:
--   $$\int_G f(g)\,d\mu_G(g)=\int_{G/H}\int_H f(xh)\,d\mu_H(h)\,d\nu(x).$$
--
--   This "unfolding" of an integral over $G$ along the cosets of $H$ is used in the source for the adelic quotients $\mathbb A_F/F$ and $\mathrm{GL}_1(\mathbb A_F)/F^\times$ (zeta integrals, theta functions) and in the proof of the Poisson summation formula (Theorem D.1.2.7), where it shows that $\widehat{f^H}$ is the restriction of $\widehat f$ to $H^\perp$.
--
--   **Deviation from the source.** The source also asserts that for every $\mu_G$-measurable $f$ the fibre integral $f^H$ is defined almost everywhere and measurable. That clause is false without an integrability or positivity assumption (for $G=H=\mathbb R$ and $f=1$ the quotient is a point of positive measure and the fibre integral diverges) and is omitted.
--
--   **Formalization Note.** `ν` is a regular Haar measure on `G ⧸ H` with the hypothesis `hν` (Weil's formula for all continuous compactly supported `φ`), which determines `ν` uniquely. The fibre integral at a coset `q` is `∫ h : H, f (q.out * h) ∂μH`, computed at the representative `q.out`; it is a Bochner integral, equal to $0$ on the $\nu$-null set of cosets where the fibre is not integrable (part 1). The Borel $\sigma$-algebra on `G ⧸ H` enters through the binders `[MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]`. Haar measures are regular (`IsHaarMeasure` together with Mathlib's `Measure.Regular`), i.e. Haar measures in the classical Radon sense of the cited references; regularity is automatic when $G$ is second countable. $G$ carries its Borel $\sigma$-algebra (`[BorelSpace G]`), and groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 747, Theorem D.1.2.1, eq. (D.1.2.1); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Theorem 1.5.3

import Mathlib

open MeasureTheory Topology

set_option autoImplicit false

namespace LCAGroup

theorem weil_quotient_integral_formula
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    (f : G → ℂ) (hf : Integrable f μ) :
    (∀ᵐ q ∂ν, Integrable (fun h : H => f (q.out * (h : G))) μH) ∧
    Integrable (fun q : G ⧸ H => ∫ h : H, f (q.out * (h : G)) ∂μH) ν ∧
    ∫ x, f x ∂μ = ∫ q : G ⧸ H, (∫ h : H, f (q.out * (h : G)) ∂μH) ∂ν := by sorry

end LCAGroup
