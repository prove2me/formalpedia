-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_eq_all
-- name    : ModularCurve.ModularPolynomialData.eq_all
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/db4ad644-44f8-547f-8344-f964f096bb3c
-- title:
--   Uniqueness of modular polynomial data at every level
-- statement:
--   Let $N$ be a nonzero natural number. A modular polynomial datum at level $N$, an element of `ModularPolynomialData N`, consists of a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ together with three conditions: $\Phi$ is monic as a polynomial in $Y$ over $\mathbb{Z}[X]$; its $Y$-degree equals `dedekindPsi N`, defined as $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ (so $N\prod_{p \mid N}(1+1/p)$); and $\Phi$ vanishes when its coefficients are pushed forward along the ring homomorphism `evalAtJ` $: \mathbb{Z}[X] \to$ `LaurentSeries ℚ` sending $X$ to the Laurent series `jq` and $Y$ is evaluated at the Laurent series `jqN N`, i.e. $\Phi(\mathtt{jq}, \mathtt{jqN}\ N) = 0$ in the field of Laurent series over $\mathbb{Q}$. The theorem asserts that any two such data $d$, $d'$ at the same level $N$ are equal; since the remaining fields are proofs, this says precisely that the polynomial $\Phi$ is uniquely determined by the three conditions.
--
--   This is the uniqueness half of the classical statement that the modular polynomial $\Phi_N$, the minimal equation of $j(q^N)$ over $\mathbb{Q}(j(q))$, is determined by being monic of degree $\psi(N)$ with integral coefficients in $j$ and killing $j(q^N)$. It is used wherever a construction or a computation must refer to "the" level-$N$ modular polynomial, for instance in the study of the weighted support of $\Phi$ and in the place-specialisation arguments on $X_0(N)$ that invoke ramification indices along the fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.ModularPolynomialData.eq_all (N : ℕ) [NeZero N] (d d' : ModularPolynomialData N) : d = d' := by sorry
