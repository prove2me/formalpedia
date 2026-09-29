-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_c_top
-- name    : ModularCurve.PhiGen.PhiGenDescends.c_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/679e8f7f-28d0-5e3a-af3d-681efa6851fa
-- title:
--   Descended coefficient family has top coefficient 1
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a prime number, let $\zeta$ be a unit of $K$, and let $c : \mathbb{N} \to \mathbb{Q}((t))$ be a family of rational Laurent series. Assume `PhiGenDescends ℓ ζ c`, that is: for every natural number $k$, the coefficient of $X^k$ in the polynomial $\prod_{i : \mathrm{Fin}(\ell+1)} (X - C(\mathrm{conj}\ \ell\ \zeta\ i))$ over $K((t))$ — where the conjugate family `conj` is given by the coset substitution `cosetSubst` applied to $\zeta$, to the coset data `cosetA ℓ i`, `cosetB ℓ i` and to the coefficientwise image over $K$ of the series `jq` — is equal to the image under `coeffEmb K` (the coefficientwise ring map induced by $\mathbb{Q} \to K$ on Laurent series) of `qExpand ℚ ℓ (c k)`, the Laurent series obtained from $c\,k$ by multiplying all exponents by $\ell$, i.e. by substituting $t \mapsto t^{\ell}$. The conclusion is that $c(\ell+1) = 1$ in $\mathbb{Q}((t))$, reflecting that the displayed product is monic of degree $\ell+1$. The proof uses the commutation of `coeffMap` with `qExpand` and the injectivity of `coeffEmb`.
--
--   This records the normalisation of the descended coefficient family attached to the modular equation of level $\ell$: the top coefficient of the polynomial whose roots are the conjugates is $1$. It feeds into [`ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq`](thm.html#ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq) and into the weighted support bound [`ModularCurve.ModularPolynomialData.weighted_support_le`](thm.html#ModularCurve.ModularPolynomialData.weighted_support_le), which package the descended coefficients as modular polynomial data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_c_top.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.PhiGenDescends.c_top {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) : c (ℓ + 1) = 1 := by sorry
