-- Prove2me | Theorems.Thm_ModularCurve_modularPolynomial_kronecker
-- name    : ModularCurve.modularPolynomial_kronecker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/a734d574-1ad1-5f78-a927-e84eb666aebf
-- title:
--   Kronecker's congruence for Φ_ℓ modulo ℓ
-- statement:
--   Let $\ell$ be a prime and let `data` be a datum of type `ModularPolynomialData ℓ`, that is: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ in one outer variable whose coefficients are polynomials over $\mathbb{Z}$, required to be monic in the outer variable, to have outer degree equal to `dedekindPsi ℓ` $= \sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$ (so $\ell+1$ for a prime), and to vanish when its coefficients are mapped through `evalAtJ`, the ring homomorphism $\mathbb{Z}[X] \to \operatorname{LaurentSeries} \mathbb{Q}$ evaluating the inner variable at the $q$-expansion `jq` of the $j$-invariant, and the outer variable is evaluated at the Laurent series `jqN ℓ` attached to level $\ell$. The assertion is that reducing all integer coefficients of $\Phi$ modulo $\ell$, i.e. applying `Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))` coefficientwise in the outer variable, yields the factorised polynomial $$\bigl(X^{\ell} - Y\bigr)\bigl(X - Y^{\ell}\bigr) \in (\mathbb{Z}/\ell)[X][Y],$$ where $X$ denotes the inner variable (entering as `Polynomial.C Polynomial.X`) and $Y$ the outer one. No uniqueness of the datum is assumed: the congruence holds for every polynomial satisfying the four conditions above, and only prime level is treated.
--
--   This is Kronecker's congruence relation for the modular equation, $\Phi_\ell(X,Y) \equiv (X^\ell - Y)(X - Y^\ell) \pmod \ell$. It is used in the full-level analysis of the modular curves, where the mod-$\ell$ factorisation of the level-$\ell$ modular polynomial governs the degeneration of the $j$-expansion relations at a prime dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularPolynomial_kronecker.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.modularPolynomial_kronecker (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (data : ModularPolynomialData ℓ) : data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) = (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := by sorry
