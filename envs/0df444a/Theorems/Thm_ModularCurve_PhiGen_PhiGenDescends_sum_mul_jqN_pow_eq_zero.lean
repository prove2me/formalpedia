-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero
-- name    : ModularCurve.PhiGen.PhiGenDescends.sum_mul_jqN_pow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/91ac86c2-21b0-512a-8404-c805a4d56b52
-- title:
--   Descended coefficients annihilate j(q^ℓ)
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a prime, let $\zeta$ be a unit of $K$, and let $c : \mathbb{N} \to$ `LaurentSeries ℚ` be a family of Laurent series over $\mathbb{Q}$. Assume `PhiGenDescends ℓ ζ c`, that is: for every $k$, the $k$-th coefficient of the polynomial $\prod_{i : \mathrm{Fin}(\ell+1)} (X - C(\mathtt{conj}\,\ell\,\zeta\,i))$ over `LaurentSeries K` — where the $i$-th conjugate is `cosetSubst ζ (cosetA ℓ i) (cosetB ℓ i)` applied to the image of the $q$-expansion `jq` under the coefficientwise embedding `coeffEmb K` — is equal to `coeffEmb K (qExpand ℚ ℓ (c k))`, the image under that embedding of the series obtained from $c_k$ by the substitution $q \mapsto q^{\ell}$. The conclusion is the identity $\sum_{k=0}^{\ell+1} c_k \cdot (\mathtt{jqN}\ \ell)^k = 0$ in `LaurentSeries ℚ`, where $\mathtt{jqN}\ \ell = \mathtt{qExpand}\ \mathbb{Q}\ \ell\ \mathtt{jq}$ is the $q$-expansion of $j$ with $q$ replaced by $q^{\ell}$.
--
--   This is the vanishing $\Phi_{\ell}(j(q), j(q^{\ell})) = 0$ of the modular equation of level $\ell$, recorded at the level of Laurent series and before the coefficients $c_k$ are identified as polynomials in $j$. It is used in the construction of the modular polynomial data for $X_0(\ell)$, namely by [`ModularCurve.ModularPolynomialData.weighted_support_le`](thm.html#ModularCurve.ModularPolynomialData.weighted_support_le) and [`ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq`](thm.html#ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.PhiGenDescends.sum_mul_jqN_pow_eq_zero {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) : ∑ k ∈ Finset.range (ℓ + 2), c k * (jqN ℓ) ^ k = 0 := by sorry
