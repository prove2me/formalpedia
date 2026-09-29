-- Prove2me | Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
-- name    : ModularCurve.nonempty_modularPolynomialData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/43c4021c-080c-5aaf-8e3d-32ee4852f077
-- title:
--   Existence of a modular polynomial datum at every level N
-- statement:
--   Let $N$ be a natural number, assumed nonzero. The assertion is that the type [`ModularCurve.ModularPolynomialData N`](def/ModularCurve_X0.html#L215) is inhabited, i.e. that there exists a datum consisting of a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$, that is an element of `Polynomial (Polynomial ℤ)`, together with proofs of three conditions: $\Phi$ is monic as a polynomial in the outer variable over the coefficient ring $\mathbb{Z}[X]$; its natural degree in that variable equals `dedekindPsi N`, defined as the sum $\sum_{d \mid N,\ d \text{ squarefree}} N/d$; and $\Phi$ vanishes when its coefficients are transported by the ring homomorphism `evalAtJ` and the outer variable is evaluated at `jqN N`. Here `evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ` is the homomorphism sending $X$ to the Laurent series `jq` (the $q$-expansion of $j$) and `jqN N` is the Laurent series obtained from $j$ at $q^N$, so the last condition says $\Phi(j(q), j(q^N)) = 0$ as an identity of Laurent series over $\mathbb{Q}$. No further hypotheses are imposed.
--
--   This is the existence of the classical modular polynomial $\Phi_N$ relating $j(q)$ and $j(q^N)$, monic of degree $\psi(N)$ in the second variable with coefficients in $\mathbb{Z}[j]$; it is the input from which the integral model of $X_0(N)$ used throughout the project is built. It is cited very widely downstream, for instance in the construction of Hecke correspondences and of the models of $X_0(N)$ in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_modularPolynomialData.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.nonempty_modularPolynomialData (N : ℕ) [NeZero N] :
    Nonempty (ModularCurve.ModularPolynomialData N) := by sorry
