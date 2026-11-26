-- Prove2me | Theorems.Thm_MuirheadMST_bartlett_decomposition
-- name    : MuirheadMST.bartlett_decomposition
-- status  : Open
-- author  : @domodus
-- created : 2026-11-26T17:37:36.90428+00:00
-- url     : https://prove2.me/theorems/f9b70eb3-cf73-5166-8b68-3e194ac7aa51
-- title:
--   Theorem 3.2.14: Bartlett's decomposition of $W_m(n,I_m)$
-- statement:
--   Let $1\le m\le n$. Let $T=(t_{ij})$ be a random upper-triangular $m\times m$ matrix with independent entries: for $i=1,\dots,m$, $t_{ii}=\|g_i\|$ with $g_i$ a standard Gaussian vector in $\mathbb R^{n-i+1}$, so that $t_{ii}^2\sim\chi^2_{n-i+1}$; and $t_{ij}\sim N(0,1)$ for $i<j$. Then
--
--   $$
--   T^{\mathsf T}T\sim W_m(n,I_m).
--   $$
--
--   Muirhead states the decomposition in the other direction: if $A\sim W_m(n,I_m)$ and $A=T^{\mathsf T}T$ with $T$ upper triangular with positive diagonal, then the $t_{ij}$ are independent with the laws above. The two directions are equivalent because a positive definite matrix has exactly one such factorization, depending measurably on the matrix, and $A$ is positive definite almost surely when $n\ge m$. This statement uses the constructive direction because Mathlib has no Cholesky factorization; deducing the source's direction from it additionally requires that uniqueness and measurability fact.
--
--   Bartlett's decomposition reduces Wishart computations to independent chi-square and normal variables; for example $\det A=\prod_i t_{ii}^2$ is a product of independent $\chi^2_{n-i+1}$ variables.
--
--   **Formalization Note** Indices start at $0$ in Lean, so $g_i\in\mathbb R^{n-i}$ there. The $N(0,1)$ entries are sampled as a full $m\times m$ array of which only the entries above the diagonal are used.
-- source:
--   R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley, 1982 (reprinted 2005, same pagination), https://doi.org/10.1002/9780470316559, §3.2.4 'Bartlett's Decomposition and the Generalized Variance', Theorem 3.2.14, p. 99 (stated there for the triangular factor of A ~ W_m(n, I_m); this is the equivalent constructive direction)

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory ProbabilityTheory

namespace MuirheadMST

theorem bartlett_decomposition (m n : ℕ) (hmn : m ≤ n) :
    (bartlettLaw m n).map (fun ω j k => ∑ i, bartlettFactor ω i j * bartlettFactor ω i k) =
      wishart m n 1 := by sorry

end MuirheadMST
