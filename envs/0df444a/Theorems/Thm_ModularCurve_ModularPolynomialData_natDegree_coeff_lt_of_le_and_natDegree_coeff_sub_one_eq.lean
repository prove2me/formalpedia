-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq
-- name    : ModularCurve.ModularPolynomialData.natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/16a39715-620d-572e-8fe6-aba14914c288
-- title:
--   Strict degree bounds for the modular polynomial near j=∞
-- statement:
--   Let $N$ be a positive integer with $2 \le N$, and write $\psi(N)$ for `dedekindPsi N`, defined as $\sum_{d \mid N,\ d \text{ squarefree}} N/d$. Let `data` be a modular polynomial datum of level $N$: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic in $Y$, has $Y$-degree exactly $\psi(N)$, and vanishes when $X$ is specialised to the $q$-expansion $j(q)$ (the ring map `evalAtJ` on $\mathbb{Z}[X]$, with values in the Laurent series over $\mathbb{Q}$) and $Y$ to `jqN N`, the $q$-expansion of $j$ at level $N$. Writing $\Phi = \sum_k a_k(X) Y^k$ with $a_k =$ `data.Φ.coeff k`, the conclusion is the conjunction of three assertions: first, for every natural number $k$ with $k + 2 \le \psi(N)$, the degree of $a_k$ is strictly less than $N\,(\psi(N) - k)$ (truncated subtraction of naturals); second, $a_{\psi(N)-1}$ has degree exactly $N$; and third, its leading coefficient is $-1$.
--
--   This is the statement that the Newton polygon of the classical modular polynomial $\Phi_N$ at $X = \infty$ has a single branch of slope $N$, corresponding to the root $j(N\tau)$: it sharpens the weighted degree bound $\deg a_k \le N(\psi(N)-k)$ to an equality only for $k = \psi(N)$ and $k = \psi(N)-1$, with leading coefficient $-1$ in the latter case. It is used in the computation of ramification indices for the map from the modular curve of level $N$ to the $j$-line along the cusp, in the three declarations on ramification indices along the inclusion of $\Gamma_0$ that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Polynomial

theorem ModularCurve.ModularPolynomialData.natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (data : ModularPolynomialData N) :
    (∀ k : ℕ, k + 2 ≤ dedekindPsi N → (data.Φ.coeff k).natDegree < N * (dedekindPsi N - k)) ∧
      (data.Φ.coeff (dedekindPsi N - 1)).natDegree = N ∧
      (data.Φ.coeff (dedekindPsi N - 1)).leadingCoeff = -1 := by sorry
