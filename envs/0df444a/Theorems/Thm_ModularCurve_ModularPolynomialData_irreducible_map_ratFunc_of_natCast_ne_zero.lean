-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
-- name    : ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/07310e9e-2539-5892-b6fb-ac5576691e55
-- title:
--   Irreducibility of the modular polynomial over K(X)
-- statement:
--   Let $K$ be a field and let $N$ be a natural number with $N \neq 0$. Let `data` be a datum of type `ModularPolynomialData N`, that is, a polynomial $\Phi \in \mathbb{Z}[X][Y]$ (an element of `Polynomial (Polynomial ℤ)`) subject to three conditions: $\Phi$ is monic as a polynomial in $Y$; its degree in $Y$ equals `dedekindPsi N`, defined as $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ (the Dedekind $\psi$-function $N\prod_{p \mid N}(1 + 1/p)$); and $\Phi$ vanishes when evaluated, via `Polynomial.eval₂`, at the ring homomorphism `evalAtJ` $\colon \mathbb{Z}[X] \to$ `LaurentSeries ℚ` sending $X$ to the Laurent series `jq`, together with the Laurent series `jqN N` substituted for $Y$. Assume further that the image of $N$ in $K$ is nonzero. Then the polynomial obtained from $\Phi$ by reducing its integer coefficients along $\mathbb{Z} \to K$, coefficientwise in $X$, and then mapping $K[X]$ into the rational function field $K(X)$ via the structure map, is irreducible as an element of $K(X)[Y]$.
--
--   This is the irreducibility of the modular equation $\Phi_N(X,Y)$ over the rational function field in characteristic zero and, for residue characteristics not dividing $N$, Igusa's theorem; equivalently, $\Phi_N(j(q),Y)$ is the minimal polynomial over $K(j(q))$ of the generator of the level-$N$ function field, of degree $\psi(N)$. It underlies the identification of the modular polynomial with the defining equation of $X_0(N)$ and is used throughout the subsequent study of places and specialisations of that model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hNK : (N : K) ≠ 0) :
    Irreducible ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))) := by sorry
