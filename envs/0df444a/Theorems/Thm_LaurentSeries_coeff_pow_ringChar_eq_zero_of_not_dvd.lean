-- Prove2me | Theorems.Thm_LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd
-- name    : LaurentSeries.coeff_pow_ringChar_eq_zero_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/60c30394-bc70-5890-b055-8aa6a6489c9f
-- title:
--   Vanishing coefficients of ℓ-th powers in characteristic ℓ
-- statement:
--   Let $K$ be a commutative ring and let $\ell$ be a prime natural number such that $K$ has characteristic $\ell$. Let $g$ be a formal Laurent series over $K$, i.e. an element of `LaurentSeries K`, the Hahn series ring with value group $\mathbb{Z}$ and coefficients in $K$, so that $g$ has coefficients $g.\mathrm{coeff}\,k$ indexed by $k \in \mathbb{Z}$ with well-ordered support. Let $n$ be an integer which is not divisible by $\ell$ (the divisibility being taken in $\mathbb{Z}$, with $\ell$ cast into $\mathbb{Z}$). The conclusion is that the coefficient of $g^{\ell}$ at index $n$ vanishes: $(g^{\ell}).\mathrm{coeff}\,n = 0$. Thus the $\ell$-th power of any Laurent series in characteristic $\ell$ is supported in $\ell\mathbb{Z}$; the statement records only this vanishing, not the full formula $g^{\ell} = \sum_k (g.\mathrm{coeff}\,k)^{\ell} q^{\ell k}$.
--
--   This is the elementary half of the Frobenius description of $\ell$-th powers of Laurent series: an $\ell$-th power in $K((q))$ has support contained in $\ell\mathbb{Z}$, so contrapositively a series with a nonzero coefficient at an index prime to $\ell$ is not an $\ell$-th power. It is used in the construction of a finite generating set for an order subalgebra in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_orderSubalgebra_finite_span_eq_top`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_orderSubalgebra_finite_span_eq_top), where a $q$-expansion not supported on $\ell\mathbb{Z}$ provides a separating element in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem LaurentSeries.coeff_pow_ringChar_eq_zero_of_not_dvd
    {K : Type u} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (g : LaurentSeries K) (n : ℤ) (hn : ¬ (ℓ : ℤ) ∣ n) :
    (g ^ ℓ).coeff n = 0 := by sorry
