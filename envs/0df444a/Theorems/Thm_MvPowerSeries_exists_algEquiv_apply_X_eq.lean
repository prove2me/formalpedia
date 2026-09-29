-- Prove2me | Theorems.Thm_MvPowerSeries_exists_algEquiv_apply_X_eq
-- name    : MvPowerSeries.exists_algEquiv_apply_X_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/16f7d245-6d09-5c60-a53d-294fcd6643c4
-- title:
--   Formal inverse function theorem in two variables
-- statement:
--   Let $W$ be a commutative ring and let $f : \mathrm{Fin}\,2 \to W[[X_0,X_1]]$ be a pair of formal power series in two variables over $W$. Assume, first, that each $f_i$ has vanishing constant coefficient, and, second, that the $2\times 2$ matrix whose $(i,j)$ entry is the coefficient of the monomial $X_j$ in $f_i$ — that is, the coefficient indexed by the finitely supported function $\mathrm{single}\,j\,1$ — has determinant a unit of $W$. The conclusion is that there exists a $W$-algebra automorphism $e$ of $W[[X_0,X_1]]$ with $e(X_i) = f_i$ for both $i$. Thus, under the stated conditions on constant terms and on the linear part, substitution of the $f_i$ for the variables is an automorphism of the two-variable power series ring. The statement is purely existential: no uniqueness of $e$, and no description of its inverse, is asserted.
--
--   This is the existence half of the formal inverse function theorem for power series in two variables over an arbitrary commutative ring, the invertibility hypothesis being on the Jacobian matrix at the origin. It is used to normalise local equations: an automorphism carrying the variables to a tangentially adapted pair of series identifies a quotient $W[[X_0,X_1]]/(F)$ with the quotient by the transformed equation, which is how the crossing model $W[[u,v]]/(uv + c)$ is recognised in the arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_algEquiv_apply_X_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries

theorem MvPowerSeries.exists_algEquiv_apply_X_eq
    {W : Type*} [CommRing W] (f : Fin 2 → MvPowerSeries (Fin 2) W)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (h1 : IsUnit (Matrix.det (Matrix.of fun i j : Fin 2 => MvPowerSeries.coeff (Finsupp.single j 1) (f i)))) :
    ∃ e : MvPowerSeries (Fin 2) W ≃ₐ[W] MvPowerSeries (Fin 2) W, ∀ i, e (MvPowerSeries.X i) = f i := by sorry
