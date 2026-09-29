-- Prove2me | Theorems.Thm_ModularCurve_aeval_lambdaModC_intCoeffs_descent
-- name    : ModularCurve.aeval_lambdaModC_intCoeffs_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/0237cdee-94f0-5d39-bf58-30280a8e44c1
-- title:
--   Integrality descent for polynomials in the λ-series
-- statement:
--   Let $\lambda \in \mathbb{Z}((\mathfrak q))$ be the integral Laurent series `lambdaInt`, namely the product of $\mathfrak q$ (the Hahn series with single term $1$ in degree $1$), the eighth power of the power series `etaProd`, the substitution $\mathfrak q \mapsto \mathfrak q^4$ applied to the sixteenth power of `etaProd`, and the substitution $\mathfrak q \mapsto \mathfrak q^2$ applied to `dedekindEtaUnitInv`; write $\lambda_{\mathbb Q} =$ `lambdaModC ℚ` for its image in $\mathbb{Q}((\mathfrak q))$ under the coefficientwise ring homomorphism induced by $\mathbb{Z} \to \mathbb{Q}$. The assertion is: for every polynomial $P \in \mathbb{Q}[X]$ such that the Laurent series $P(\lambda_{\mathbb Q})$, obtained by evaluating $P$ at $\lambda_{\mathbb Q}$ in the $\mathbb{Q}$-algebra $\mathbb{Q}((\mathfrak q))$, satisfies `IntCoeffs`, that is, for every integer index $m$ the coefficient of $\mathfrak q^m$ in $P(\lambda_{\mathbb Q})$ is the image of some integer, and for every natural number $k$, there exists $z \in \mathbb{Z}$ with $P.\mathrm{coeff}\,k = z$ in $\mathbb{Q}$. Since $k$ ranges over all natural numbers, this says exactly that $P$ lies in $\mathbb{Z}[X]$, phrased one coefficient at a time.
--
--   This is the elementary $\mathfrak q$-expansion descent for the normalised level-two series $\lambda$: integrality of the Laurent coefficients of $P(\lambda)$ forces integrality of the coefficients of $P$, the triangular shape of the powers $\lambda^i$ making the comparison possible. It is used in the construction of the data underlying the level-two modular polynomial, [`ModularCurve.nonempty_lambdaModularPolynomialData`](thm.html#ModularCurve.nonempty_lambdaModularPolynomialData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_aeval_lambdaModC_intCoeffs_descent.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.aeval_lambdaModC_intCoeffs_descent (P : Polynomial ℚ)
    (hP : IntCoeffs (Polynomial.aeval (lambdaModC ℚ) P)) (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ) := by sorry
