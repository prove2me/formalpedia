-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_eq_24
-- name    : HScattered.Hyperplanes.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:42.022024+00:00
-- url     : https://prove2.me/theorems/2db68b7d-9658-4600-b025-4f584528c1bd
-- title:
--   Equation (24) — $\alpha_k = \sum_{j\le k}[k\ j]_q\beta_j$
-- statement:
--   In the setting of §5.2 ($s = h+1$, $U$ an $h$-scattered $\mathbb F_q$-subspace of $V(r,q^n)$ of dimension $rn/s$), let
--   $$\alpha_k = \sum_i h_i (q^n-1) q^{ki}, \qquad \beta_k = \sum_i h_i (q^n-1)(q^i-1)(q^i-q)\cdots(q^i-q^{k-1}).$$
--   Then for every $k \in \{0, 1, \dots, s\}$,
--   $$\alpha_k = \sum_{j=0}^{k}\begin{bmatrix} k\\ j\end{bmatrix}_q \beta_j .$$
--
--   Since the $\beta_j$ are known from Lemma 5.7 and (23), this determines $\alpha_0, \dots, \alpha_s$.
--
--   **Formalization Note** $\alpha_k$, $\beta_k$ are integers, cast to $\mathbb R$ to be combined with the real-valued Gaussian binomials at $q = |\mathbb F_q|$. The paper introduces $\alpha_k$ for $k \le s-1$ but uses (24) at $k = s$ in (25), so the range $0 \le k \le s$ is stated.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 21, equation (24)

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

namespace HScattered.Hyperplanes

/-- Equation (24) (arXiv:1906.10590v2, p. 21): in the setting of §5.2 (`s = h + 1`), for
`k ∈ {0, …, s}`, `α_k = ∑_{j=0}^{k} [k j]_q β_j` with `q = |F|`. -/
theorem eq_24 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (k : ℕ) (hk : k ≤ h + 1) :
    (alphaSum F K U k : ℝ) =
      ∑ j ∈ Finset.range (k + 1),
        gaussBinom (Fintype.card F : ℝ) k j * (betaSum F K U j : ℝ) := by sorry

end HScattered.Hyperplanes
