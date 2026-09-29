-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub
-- name    : ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/c227a10a-f653-56cc-b84b-d46c3ae14769
-- title:
--   Bidegree bound deg cᵢ ≤ p(ψ(p)-i) at prime level
-- statement:
--   Let $p$ be a prime and let `data` be a modular-polynomial datum at level $p$, i.e. a bivariate polynomial $\Phi =$ `data.Φ` $\in (\mathbb{Z}[X])[Y]$ together with the data that $\Phi$ is monic in $Y$, that its degree in $Y$ equals $\psi(p) =$ `dedekindPsi p`, defined as $\sum_{d \mid p,\, d \text{ squarefree}} p/d$, and that $\Phi$ vanishes when its coefficients in $\mathbb{Z}[X]$ are mapped into the Laurent series over $\mathbb{Q}$ by $X \mapsto j(q)$ (the ring homomorphism `evalAtJ`) and $Y$ is set equal to the series `jqN p`. Assume further `EvalSymm data.Φ`: for all Laurent series $x, y$ over $\mathbb{Q}$ one has $\Phi(x, y) = \Phi(y, x)$, where the first argument is substituted into the coefficients and the second into $Y$. Then for every natural number $i$, the $i$-th coefficient $c_i \in \mathbb{Z}[X]$ of $\Phi$ viewed as a polynomial in $Y$ satisfies $\deg c_i \le p \cdot (\psi(p) - i)$, the subtraction being truncated subtraction of natural numbers (so the bound reads $0$ once $i \ge \psi(p)$, and $\deg$ is the `natDegree` convention assigning $0$ to the zero polynomial).
--
--   This is the sharp bidegree bound for the classical modular equation $\Phi_p(X,Y)$ at prime level, in the normalisation $\psi(p) = p+1$. It is used in the construction of integral models of $X_0(p)$ and of the associated cusp charts in characteristic $p$ and away from $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Polynomial

theorem ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub
    (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p)
    (hsymm : EvalSymm data.Φ) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ p * (dedekindPsi p - i) := by sorry
