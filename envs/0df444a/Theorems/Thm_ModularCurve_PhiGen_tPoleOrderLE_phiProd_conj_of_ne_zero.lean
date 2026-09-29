-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero
-- name    : ModularCurve.PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/53eb075f-fb44-5953-ac7f-20c40adc5ed4
-- title:
--   Pole bound ℓ²+ℓ-1 for non-constant coefficients
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a natural number carrying a `Fact` instance that it is prime, let $\zeta$ be a unit of $K$, and let $k$ be a non-zero natural number. Consider the family of $\ell+1$ Laurent series over $K$ given by `conj ℓ ζ`, whose $i$-th member (for $i$ in `Fin (ℓ + 1)`) is obtained by applying to `coeffEmb K jq` — the image of the Laurent series `jq` over $\mathbb{Q}$ under coefficientwise application of `algebraMap ℚ K` — the ring homomorphism `cosetSubst ζ a b` with $a =$ `cosetA ℓ i` ($=\ell$ if $i=0$, else $1$) and $b =$ `cosetB ℓ i` ($=0$ if $i=0$, else $i-1$); this homomorphism is `qTwist (ζ ^ (a * b))` followed by `qExpand K (a * a)`. Form the polynomial $\prod_{i}\bigl(X - C(\mathrm{conj}\,\ell\,\zeta\,i)\bigr)$ in `Polynomial (LaurentSeries K)`. The assertion is that its coefficient in degree $k$ satisfies `TPoleOrderLE … (ℓ * ℓ + ℓ - 1)`, that is, its $m$-th Laurent coefficient vanishes for every integer $m < -(\ell^2+\ell-1)$.
--
--   The coefficients of $\prod_i (X - \mathrm{conj}\,\ell\,\zeta\,i)$ are, up to sign, the elementary symmetric functions of the $\ell+1$ conjugates entering the modular equation of level $\ell$, and the statement bounds the order of their pole in the uniformising parameter $t$: for a coefficient of positive degree $k$ at least one of the $\ell+1$ conjugates is absent from each monomial, which improves the uniform bound $\ell^2+\ell$ by one. It feeds into [`ModularCurve.ModularPolynomialData.weighted_support_le`](thm.html#ModularCurve.ModularPolynomialData.weighted_support_le), the bound on the weighted support of the modular polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) : TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ - 1) := by sorry
