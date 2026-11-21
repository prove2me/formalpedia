-- Prove2me | Theorems.Thm_MasulloAudit_rational_prime_orbital_images_after_cutoff
-- name    : MasulloAudit.rational_prime_orbital_images_after_cutoff
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:58:25.11975+00:00
-- url     : https://prove2.me/theorems/55eb1b9f-1507-4f48-95d9-943db42ed424
-- title:
--   Rational adelic principal-value orbits fill the spherical Hilbert space after either cutoff
-- statement:
--   Fix a rational prime $p$, a locally finite Borel measure $\mu$ on the real log-norm coordinate, and a measurable mask $S\subseteq[a,\infty)$. Work on actual rational ideles with real component $e^t$ and finite component in $\widehat{\mathbb Z}^{\times}$. Let $X_p$ consist of admissible adelic Schwartz–Bruhat differences $\Phi=\Psi-\Psi(\pi_p^{-1}\,\cdot)$ where $\pi_p$ is the single-place uniformizer idele and $\Psi=f\otimes1_{\widehat{\mathbb Z}}$ is admissible with $f$ smooth and compactly supported. Admissibility means value zero at the origin and integral zero for every additive Haar measure. For any class $B$ containing $X_p$, take its rational orbital sums on these representatives and multiply by $1_S$. Their closed $L^2(\mu)$ image is
--   $$\{w\in L^2(\mu): w=0\ \text{almost everywhere outside }S\}.$$
--   This applies both to the one-prime principal-value family itself and to all admissible tests. In the rational trivial isotype the truncated closed spaces in (11.1.2.6) for the empty prime set and for $\{p\}$ therefore agree on the normalized spherical representatives, for every width and for either manuscript cutoff. The proof constructs the original tests and uses the actual local operator and the ordinary rational orbit sum.
-- source:
--   A. M. Masullo, The Music of the Primes, 20 November 2026 draft, Definition 5.3.1.2, pp. 240–241, Definition 5.3.1.4, pp. 241–242, and Theorem 11.1.2.1(2), equation (11.1.2.6), pp. 480–482. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_Masullo_RationalSphericalCutoff

open MeasureTheory Set MasulloAudit.RationalSphericalCutoff

theorem MasulloAudit.rational_prime_orbital_images_after_cutoff (p : Nat.Primes) (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (hsa : s ⊆ Set.Ici a) :
    (∀ t : ℝ, ∃ z, Representative t z) ∧
    (∀ B, primeSources p ⊆ B →
      closure (MasulloAudit.RationalSphericalCutoff.image μ s B) = supported μ s) ∧
    closure (MasulloAudit.RationalSphericalCutoff.image μ s (primeSources p)) = supported μ s ∧
    closure (MasulloAudit.RationalSphericalCutoff.image μ s {test | Admissible test}) = supported μ s := by sorry
