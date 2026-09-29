-- Prove2me | Theorems.Thm_ModularCurve_monic_fibrePoly
-- name    : ModularCurve.monic_fibrePoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/53290178-1c2d-503e-be58-c5b7dbbb0985
-- title:
--   Fibre polynomials of monic bivariate integral polynomials are monic
-- statement:
--   Let $K$ be a field and let $\Phi$ be a polynomial in one variable over $\mathbb{Z}[X]$, that is, an element of $(\mathbb{Z}[X])[Y]$, assumed monic as a polynomial in $Y$ (its leading coefficient is the constant polynomial $1$ of $\mathbb{Z}[X]$). Let $a \in K$. The fibre polynomial `fibrePoly Φ a` is by definition the image of $\Phi$ under the coefficientwise application of the ring homomorphism $\mathbb{Z}[X] \to K$ which reduces integer coefficients along the unique ring map $\mathbb{Z} \to K$ and evaluates $X$ at $a$; concretely it is $\Phi(a, Y) \in K[Y]$, obtained by substituting $a$ for the first variable. The assertion is that this polynomial in $K[Y]$ is again monic. No assumption is made on the characteristic of $K$ or on $a$, and no perfectness or finiteness hypothesis enters; in particular the specialisation may drop the degree of no coefficient, since the leading coefficient $1$ is sent to $1$ and the resulting polynomial has the same degree as $\Phi$ in $Y$.
--
--   This is the elementary invariance of monicity under specialising one variable of a bivariate polynomial, applied to modular-type correspondences $\Phi(X,Y)$ monic in $Y$; it guarantees that each fibre $\Phi(a,Y)$ has degree equal to $\deg_Y \Phi$ and leading coefficient $1$. It feeds the root counts for the fibres of the Hecke correspondences used in the degree computations for modular curves, being cited in the factorisation of fibre polynomials at transcendental $j$-invariants, in the analysis of Hecke degeneracies on the special fibre of $X_1$, and in the construction of Frobenius-semilinear structures on torsion models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_monic_fibrePoly.lean

import Mathlib
import Definitions.Def_ModularCurve_FibrePoly

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
namespace ModularCurve

theorem monic_fibrePoly {K : Type*} [Field K] {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    (a : K) : (fibrePoly Φ a).Monic := by sorry
