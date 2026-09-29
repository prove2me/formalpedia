-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs
-- name    : ModularCurve.PhiGen.PhiGenDescends.intCoeffs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/ae0a893b-f12e-59f5-a601-8cf451da577a
-- title:
--   Integrality of the descended coefficients of Φ_ℓ
-- statement:
--   Let $K$ be a field equipped with an algebra structure over $\mathbb{Q}$, let $\ell$ be a prime, let $\zeta$ be a unit of $K$, and let $c \colon \mathbb{N} \to \mathrm{LaurentSeries}\,\mathbb{Q}$ be a family of rational Laurent series. Assume `PhiGenDescends ℓ ζ c`, that is: for every $k$, the coefficient of $X^k$ in the monic polynomial $\prod_{i \in \mathrm{Fin}(\ell+1)} (X - \mathrm{conj}\,\ell\,\zeta\,i)$ over $\mathrm{LaurentSeries}\,K$ equals the image under `coeffEmb K` (the coefficientwise application of $\mathbb{Q} \to K$) of `qExpand ℚ ℓ (c k)`, the Laurent series obtained from $c_k$ by multiplying all exponents by $\ell$; here the $\ell+1$ series $\mathrm{conj}\,\ell\,\zeta\,i$ are obtained from the coefficientwise image in $K$ of the series `jq` by the substitution `cosetSubst` attached to $\zeta$ and to the data `cosetA ℓ i`, `cosetB ℓ i`. Assume further that $\zeta^\ell = 1$. Then for every $k$ the series $c_k$ satisfies `IntCoeffs`: for each $m \in \mathbb{Z}$ there is an integer $z$ with $c_k$'s coefficient in degree $m$ equal to the image of $z$ in $\mathbb{Q}$.
--
--   This is the integrality of the coefficients of the modular equation of prime level $\ell$: the elementary symmetric functions of the $\ell+1$ conjugates of the $q$-expansion of $j$ descend to Laurent series with integral coefficients. It feeds the construction of the modular polynomial data for $X_0(\ell)$, being used in [`ModularCurve.ModularPolynomialData.weighted_support_le`](thm.html#ModularCurve.ModularPolynomialData.weighted_support_le), [`ModularCurve.PhiGen.splits_of_prime`](thm.html#ModularCurve.PhiGen.splits_of_prime) and [`ModularCurve.exists_modularPolynomialData_evalSymm`](thm.html#ModularCurve.exists_modularPolynomialData_evalSymm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.PhiGenDescends.intCoeffs {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) : IntCoeffs (c k) := by sorry
