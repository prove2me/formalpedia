-- Prove2me | Theorems.Thm_LaurentSeries_coeff_neg_one_mul_inv_pow_uniformizer
-- name    : LaurentSeries.coeff_neg_one_mul_inv_pow_uniformizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/288b5515-ef56-59c9-ac18-c73e0d14af21
-- title:
--   Residue of ω v in characteristic q with s^q v = 1
-- statement:
--   Let $R$ be a commutative ring of prime characteristic $q$, and work in the ring $\mathrm{LaurentSeries}\ R = \mathrm{HahnSeries}\ \mathbb{Z}\ R$ of formal Laurent series with integer exponents. Let $\omega, s, v$ be three such series, subject to: $\omega.\mathrm{coeff}\ n = 0$ for every $n < 0$, so that $\omega$ is a power series; $s.\mathrm{coeff}\ 1 = 1$ and $s.\mathrm{coeff}\ n = 0$ for every $n < 1$, so that $s = z + O(z^2)$ with leading coefficient exactly $1$; and $s^q \cdot v = 1$, so that $v$ is a (two-sided) inverse of the $q$-th power of $s$. The conclusion is the equality of coefficients $$(\omega \cdot v).\mathrm{coeff}\ (-1) = \omega.\mathrm{coeff}\ ((q:\mathbb{Z}) - 1),$$ i.e. the residue, the coefficient of $z^{-1}$, of the product $\omega v = \omega/s^q$ equals the coefficient of $z^{q-1}$ in $\omega$ itself. No hypothesis beyond the above is imposed on $R$; in particular $R$ is not assumed reduced, a domain or nontrivial.
--
--   This is the statement that, in characteristic $q$, taking the residue of $\omega/s^q$ with respect to a normalised uniformiser $s$ recovers the $(q-1)$-st coefficient of $\omega$, so that the recipe is insensitive to the choice of $s$. It is used in [`WeierstrassCurve.coeff_invariantDifferential_eq_hasseInvariant`](thm.html#WeierstrassCurve.coeff_invariantDifferential_eq_hasseInvariant), where the Hasse invariant of a Weierstrass curve in characteristic $q$ is identified with a coefficient of the expansion of the invariant differential.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_coeff_neg_one_mul_inv_pow_uniformizer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.coeff_neg_one_mul_inv_pow_uniformizer {R : Type*} [CommRing R]
    (q : ℕ) [Fact q.Prime] [CharP R q]
    (ω s v : LaurentSeries R) (hω : ∀ n < 0, ω.coeff n = 0)
    (hs1 : s.coeff 1 = 1) (hs : ∀ n < 1, s.coeff n = 0) (hv : s ^ q * v = 1) :
    (ω * v).coeff (-1) = ω.coeff ((q : ℤ) - 1) := by sorry
