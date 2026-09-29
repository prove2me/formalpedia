-- Prove2me | Theorems.Thm_LaurentSeries_coeff_neg_one_inv_mul_derivative
-- name    : LaurentSeries.coeff_neg_one_inv_mul_derivative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/1b6eddae-e80e-5d94-8981-69c3c2aae52a
-- title:
--   Residue of a logarithmic derivative equals the order
-- statement:
--   Let $R$ be a commutative ring and let $f, g$ be Laurent series over $R$, i.e. elements of `LaurentSeries R` (Hahn series over $R$ with value group $\mathbb{Z}$). Let $k$ be an integer, and assume: the coefficient of $f$ in degree $k$ equals $1$; every coefficient of $f$ in a degree $n < k$ vanishes (so $f = z^{k}(1 + O(z))$, and in particular $f$ has order $k$ when $R$ is nontrivial); and $f \cdot g = 1$, so that $g$ is the inverse of $f$. The conclusion is that the coefficient in degree $-1$ of the product $g \cdot \mathrm{d}f$, where $\mathrm{d}f$ is the formal derivative `LaurentSeries.derivative R f` of $f$, is equal to the image $(k : R)$ of $k$ under the canonical ring map $\mathbb{Z} \to R$. In other words, the residue of the logarithmic derivative $f'/f$ is the order $k$ of $f$, stated with the inverse $g$ of $f$ supplied as a hypothesis rather than constructed.
--
--   This is the standard computation that the residue of the logarithmic derivative $f'/f$ of a Laurent series records its order, here in the normalised form where $f$ is monic of order $k$. It is used in the determination of the relevant Laurent coefficient of the invariant differential of a Weierstrass curve in terms of the Hasse invariant, via [`WeierstrassCurve.coeff_invariantDifferential_eq_hasseInvariant`](thm.html#WeierstrassCurve.coeff_invariantDifferential_eq_hasseInvariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_coeff_neg_one_inv_mul_derivative.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.coeff_neg_one_inv_mul_derivative {R : Type*} [CommRing R]
    (f g : LaurentSeries R) (k : ℤ) (hk : f.coeff k = 1) (hlt : ∀ n < k, f.coeff n = 0)
    (hinv : f * g = 1) :
    (g * LaurentSeries.derivative R f).coeff (-1) = (k : R) := by sorry
