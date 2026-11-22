-- Prove2me | Theorems.Thm_LCAGroup_weil_quotientMeasure_existsUnique
-- name    : LCAGroup.weil_quotientMeasure_existsUnique
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:31.433809+00:00
-- url     : https://prove2.me/theorems/927b00e9-47e7-460e-abd5-dac40c58643a
-- title:
--   Theorem D.1.2.1 — Weil's formula: the unique Haar measure $\nu$ on $G/H$ with $\int_G f\,d\mu_G=\int_{G/H}\int_H f(xh)\,d\mu_H(h)\,d\nu(x)$
-- statement:
--   **Weil's quotient integral formula: existence and uniqueness of the quotient Haar measure** (Theorem D.1.2.1 of the source, first assertion).
--
--   Let $G$ be a Hausdorff locally compact abelian group, $H\subseteq G$ a closed subgroup, $\mu_G$ a Haar measure on $G$ and $\mu_H$ a Haar measure on $H$. For a continuous compactly supported function $f\in C_c(G)$ the integral $\int_H f(xh)\,d\mu_H(h)$ depends only on the coset $xH$, and defines a continuous compactly supported function on the quotient group $G/H$. Then there exists a **unique** Haar measure $\nu$ on $G/H$ such that for every $f\in C_c(G)$
--   $$\int_G f(g)\,d\mu_G(g)=\int_{G/H}\int_H f(xh)\,d\mu_H(h)\,d\nu(x).$$
--
--   So any two of the three Haar measures $\mu_G,\mu_H,\nu$ determine the third; $\nu$ is the *quotient measure* $\mu_G/\mu_H$. The source uses this to normalise Haar measures on quotients such as $\mathbb A_F/F$ and the idele class group $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$, and as the basis of the Poisson summation formula (Theorem D.1.2.7).
--
--   **Formalization Note.** The conclusion is `∃! ν : Measure (G ⧸ H), ν.IsHaarMeasure ∧ ν.Regular ∧ ∀ φ, Continuous φ → HasCompactSupport φ → ∫ φ dμ = ∫ q, (∫ h : H, φ (q.out * h) ∂μH) ∂ν`. The inner integral at a coset `q` is computed at the representative `q.out` (`Quotient.out`); by left invariance of $\mu_H$ it does not depend on the representative. Uniqueness is among regular Haar measures on the Borel $\sigma$-algebra of the quotient topology on `G ⧸ H`; this $\sigma$-algebra enters through the binders `[MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]`, which take precedence over Mathlib's default quotient $\sigma$-algebra (the two agree when $G$ is Polish). The subgroup $H$ carries the subspace topology and its Borel $\sigma$-algebra. Haar measures are regular (`IsHaarMeasure` together with Mathlib's `Measure.Regular`), i.e. Haar measures in the classical Radon sense of the cited references; regularity is automatic when $G$ is second countable. $G$ carries its Borel $\sigma$-algebra (`[BorelSpace G]`), and groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 747, Theorem D.1.2.1, eq. (D.1.2.1); classical reference: S. Lang, Real and Functional Analysis, Third Edition, Springer, Ch. XII, Theorem 4.1 and Corollary 2.4

import Mathlib

open MeasureTheory Topology

set_option autoImplicit false

namespace LCAGroup

theorem weil_quotientMeasure_existsUnique
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular] :
    ∃! ν : Measure (G ⧸ H), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
        ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν := by sorry

end LCAGroup
