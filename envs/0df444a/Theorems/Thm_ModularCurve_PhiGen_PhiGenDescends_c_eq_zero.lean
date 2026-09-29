-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero
-- name    : ModularCurve.PhiGen.PhiGenDescends.c_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/51d81ec6-fd61-5d61-b37b-89a26b0b5480
-- title:
--   Vanishing of descended coefficients above degree ℓ+1
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a prime, let $\zeta$ be a unit of $K$, and let $c \colon \mathbb{N} \to \mathrm{LaurentSeries}\,\mathbb{Q}$ be a family of rational Laurent series. Assume `PhiGenDescends ℓ ζ c`, that is: for every $k \in \mathbb{N}$, the coefficient of $X^k$ in the polynomial $\prod_{i \in \mathrm{Fin}(\ell+1)} \bigl(X - \mathrm{C}(\mathtt{conj}\ \ell\ \zeta\ i)\bigr)$ over $\mathrm{LaurentSeries}\,K$ — where the $i$-th root `conj ℓ ζ i` is the coset substitution determined by $\zeta$ and the data `cosetA ℓ i`, `cosetB ℓ i` applied to the image of `jq` under the coefficientwise map `coeffEmb K` induced by $\mathbb{Q} \to K$ — equals `coeffEmb K (qExpand ℚ ℓ (c k))`, the image in $\mathrm{LaurentSeries}\,K$ of the $\ell$-fold $q$-expansion rescaling of $c\,k$ (the ring endomorphism of Laurent series multiplying all exponents by $\ell$). Then for every $k$ with $\ell + 1 < k$ one has $c\,k = 0$.
--
--   This records that a family of rational Laurent series descending the product of the $\ell+1$ conjugates is supported in degrees at most $\ell+1$, the product being a monic polynomial of degree $\ell+1$; it is the degree bound used in the construction of the modular polynomial data, and it is cited by [`ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq`](thm.html#ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.PhiGenDescends.c_eq_zero {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) {k : ℕ} (hk : ℓ + 1 < k) : c k = 0 := by sorry
