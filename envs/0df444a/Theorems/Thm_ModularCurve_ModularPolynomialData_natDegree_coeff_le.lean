-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le
-- name    : ModularCurve.ModularPolynomialData.natDegree_coeff_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/ba4c65b9-77b0-5ad8-8119-d1b874910190
-- title:
--   Degree bound p+1 for the coefficients of Φₚ
-- statement:
--   Let $p$ be a prime and let `data` be a modular polynomial datum of level $p$, that is: a polynomial $\Phi =$ `data.Φ` in `Polynomial (Polynomial ℤ)`, viewed as an element of $\mathbb{Z}[X][Y]$, which is monic in the outer variable $Y$, whose degree in $Y$ equals $\psi(p)$, where $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ is the function `dedekindPsi`, and which satisfies the vanishing relation `Φ.eval₂ evalAtJ (jqN p) = 0`: substituting the formal $q$-expansion of $j$ for the inner variable (via the ring homomorphism `evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ` determined by $X \mapsto$ `jq`) and the series `jqN p` for the outer variable gives $0$ in the Laurent series over $\mathbb{Q}$. The assertion is that for every natural number $k$, the coefficient of $Y^k$ in $\Phi$, an element of $\mathbb{Z}[X]$, has degree at most $p+1$; that is, each $Y^k$-coefficient $c_k(X)$ of $\Phi_p$ satisfies $\deg_X c_k \le p+1$. No bound better than $p+1$ is claimed, and the bound is stated uniformly in $k$, including $k$ exceeding the $Y$-degree.
--
--   This is the standard degree bound on the modular polynomial of prime level: $\Phi_p(X,Y)$ has degree at most $p+1 = \psi(p)$ in each of its two variables. It is used in the analysis of the places of the modular curve $X_0(p)$ lying over a given value of $j$, in particular in the counting of ramification indices in the fibres, and in the refined coefficient-degree estimates for $\Phi_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Polynomial

theorem ModularCurve.ModularPolynomialData.natDegree_coeff_le (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (k : ℕ) : (data.Φ.coeff k).natDegree ≤ p + 1 := by sorry
