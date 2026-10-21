-- Prove2me | Theorems.Thm_MatrixAnalytic_SkipFree_G_structure
-- name    : MatrixAnalytic.SkipFree.G_structure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:36.040047+00:00
-- url     : https://prove2.me/theorems/b764c432-d88a-40ab-a227-a5195b079f31
-- title:
--   Theorem 13.1.3 — the matrix G of the QBD embedding an M/G/1-type chain has first block column H, H², H³, …
-- statement:
--   Let $D_0,D_1,\dots$ and $C_0,C_1,\dots$ be the blocks of an M/G/1-type Markov chain with transition matrix (13.1), and consider the QBD (13.3) with blocks (13.4)–(13.7) on the states $(n,d,j)$ (level $n$, phase $(d,j)$). Fix a level $n\ge1$, let $G$ be the matrix of first passage probabilities from $\ell(n)$ to $\ell(n-1)$ of this QBD, indexed by the phases $(k,i)$ and $(d,j)$, and let $H$ be the matrix (13.9),
--   $$H_{ij}=\mathrm P[\tau<\infty\ \&\ (X_\tau,D_\tau,J_\tau)=(n-1,0,j)\mid(X_0,D_0,J_0)=(n,0,i)].$$
--   Then $G$ has the structure (13.8):
--   $$G=\begin{bmatrix}H&0&0&\cdots\\H^2&0&0&\cdots\\H^3&0&0&\cdots\\\vdots&\vdots&\vdots&\ddots\end{bmatrix},\qquad\text{i.e.}\qquad G_{(k,i),(d,j)}=\begin{cases}(H^{k+1})_{ij}&d=0,\\0&d\ge1.\end{cases}$$
--
--   The structure reduces the QBD's first-passage matrix, which has infinitely many phases, to the $m\times m$ matrix $H$, and is the step from Theorem 8.1.4 to the equation (13.10) for $H$.
--
--   **Formalization Note** Products of nonnegative matrices are computed in $[0,\infty]$. The statement is made at every level $n\ge1$, with $H$ taken at the same level. The transition matrix (13.1) is assumed stochastic; the phase set is arbitrary.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 271–272, Theorem 13.1.3

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models

open scoped ENNReal

namespace MatrixAnalytic.SkipFree

/-- Theorem 13.1.3 (pp. 271–272). For the QBD (13.3) with blocks (13.4)–(13.7) embedding an
M/G/1-type chain (13.1), and every level `n ≥ 1`, the first-passage matrix `G` from `ℓ(n)` to
`ℓ(n − 1)` has the structure (13.8): its block column for sublevel `0` is `H, H², H³, …` and all
its other block columns are zero, i.e. `G_{(k,i),(d,j)} = (H^{k+1})_{ij}` if `d = 0` and `0`
otherwise, where `H` is the matrix (13.9) at level `n`. Products are computed in `ℝ≥0∞`. -/
theorem G_structure {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ)
    (hP : IsStochasticC (mg1P D C)) (n : ℕ) (hn : 1 ≤ n) :
    ∀ (k : ℕ) (i : ι) (d : ℕ) (j : ι),
      matG (mg1QBD D C) n (k, i) (d, j) =
        if d = 0 then matPowE (matH D C n) (k + 1) i j else 0 := by sorry

end MatrixAnalytic.SkipFree
