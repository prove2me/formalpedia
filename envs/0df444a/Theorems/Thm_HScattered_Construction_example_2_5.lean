-- Prove2me | Theorems.Thm_HScattered_Construction_example_2_5
-- name    : HScattered.Construction.example_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:31.343586+00:00
-- url     : https://prove2.me/theorems/2c6cc3db-1d73-438a-9cc6-ba2bdf06a7b1
-- title:
--   Example 2.5 — {(x, x^q, …, x^{q^{r−1}})} is maximum (r − 1)-scattered of dimension n when n ≥ r
-- statement:
--   Let $2\le r\le n$, where $n=[\mathbb F_{q^n}:\mathbb F_q]$. In $\mathbb F_{q^n}^{\,r}$ the $\mathbb F_q$-subspace
--
--   $$
--   G_r=\{(x,x^{q},x^{q^2},\dots,x^{q^{r-1}}) : x\in\mathbb F_{q^n}\}
--   $$
--
--   is maximum $(r-1)$-scattered, and $\dim_{\mathbb F_q}G_r=n$.
--
--   These subspaces come from Gabidulin codes; they are the building blocks of the construction in Theorem 2.6, applied with $r=h+1$.
--
--   **Formalization Note** The paper's $r$ is unrestricted, but $(r-1)$-scattered requires $0<r-1$ by Definition 1.1, so $r\ge2$ is added. The hypothesis $n\ge r$ is the paper's and is essential: for $n<r$ the subspace has dimension $n<r$ and cannot span $\mathbb F_{q^n}^{\,r}$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 7, Example 2.5

import Mathlib
import Definitions.Def_HScattered_Construction_IsHScattered
import Definitions.Def_HScattered_Construction_gabidulinSubspace

namespace HScattered.Construction

/-- Example 2.5 (arXiv:1906.10590v2, p. 7): in `𝔽_{qⁿ}^r`, `r ≥ 2`, if `n ≥ r` then the
`𝔽_q`-subspace `{(x, x^q, x^{q²}, …, x^{q^{r−1}}) : x ∈ 𝔽_{qⁿ}}` is maximum (r − 1)-scattered of
dimension `n`. -/
theorem example_2_5 {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    (r : ℕ) (hr : 2 ≤ r) (hn : r ≤ Module.finrank F K) :
    IsMaximumHScattered F K (r - 1) (gabidulinSubspace F K r) ∧
      Module.finrank F (gabidulinSubspace F K r) = Module.finrank F K := by sorry

end HScattered.Construction
