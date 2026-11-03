-- Prove2me | Theorems.Thm_NearestDSM_theorem_3_9
-- name    : NearestDSM.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:46.669857+00:00
-- url     : https://prove2.me/theorems/4d7b8133-f4f1-4217-8bdd-f550eb7e7c05
-- title:
--   Theorem 3.9 — the equivalence class is the polyhedron (3.8)
-- statement:
--   Let $\tilde y\in\mathbb R^{2n-1}$, let $X^1,\dots,X^K$ be the blocks of $\mathrm{Mat}(\hat x+A^T\tilde y)_+$ (the last containing the last row) and $U=[u^1\cdots u^K]$ as in (3.6)–(3.7). The equivalence class $[\tilde y]$ is a polyhedron, given by
--   $$
--   [\tilde y]=\{y\in\mathbb R^{2n-1}\mid y=\tilde y+U\lambda\ \text{for some }\lambda\in\mathbb R^K,\ \lambda_K=0,\ Y^{ij}\le 0\ \text{for } i\ne j\},
--   $$
--   where $Y^{ij}$ is the $(i,j)$ block of $Y=\mathrm{Mat}(\hat x+A^Ty)$ for the partition associated with $\tilde y$.
--
--   Both claims are stated: the displayed description, and that $[\tilde y]$ is the solution set of finitely many linear inequalities.
--
--   **Formalization Note** Blocks are connected components; entry $(a,b)$ is in an off-diagonal block when row $a$ and column $b$ lie in different components. A polyhedron is a set $\{y:\langle g_i,y\rangle\le h_i,\ i=1,\dots,m\}$ (an equation counts as two inequalities).
--
--   Differences from the source:
--   - encoding: blocks of (3.2) and the last block $X^K$ → connected components of the bipartite graph of $\mathrm{Mat}(\hat x+A^T\tilde y)_+$, last block = component of the last row; $U\lambda=\sum_\kappa\lambda_\kappa u^\kappa$; reason: the same partition and the same set
--   - encoding: "is a polyhedron" → equal to $\{y:\langle g_i,y\rangle\le h_i\ \forall i\}$ for finitely many $(g_i,h_i)$; reason: definition of a polyhedron
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Theorem 3.9 and (3.8), p.16

import Mathlib
import Definitions.Def_NearestDSM_equivClass
import Definitions.Def_NearestDSM_blockShift
import Definitions.Def_NearestDSM_lastBlock
open Classical

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Theorem 3.9, p.16. Let `ỹ ∈ ℝ^{2n−1}`. The equivalence class `[ỹ]` is a
polyhedron given by
`[ỹ] = {y | y = ỹ + Uλ for some λ ∈ ℝ^K, λ_K = 0 and Y^{ij} ≤ 0 for i ≠ j}` (3.8),
where `Y^{ij}` is the `(i, j)` block of `Y = Mat(x̂ + Aᵀy)` with respect to the partition
associated with `ỹ` (3.2).

**Formalization Note.** Blocks are the connected components `κ` of the bipartite graph of
`Mat(x̂ + Aᵀỹ)₊`, `U λ = ∑_κ λ_κ u^κ` with `u^κ = blockShift Xh ỹ κ`, `λ_K` is the coefficient of
the last block (`lastBlock`), and entry `(a, b)` lies in an off-diagonal block iff row `a` and
column `b` are in different components. "Is a polyhedron" is the second conjunct: `[ỹ]` is the
solution set of finitely many linear inequalities `⟪g_i, y⟫ ≤ h_i` (an equation is two of them).
The sum over components uses classical decidability. The paper's size `n` is `n + 1`. -/
theorem theorem_3_9 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (yt : Dual n) :
    equivClass Xh yt =
        {y | ∃ lam : (bipGraph (Xmat Xh yt)).ConnectedComponent → ℝ, lam (lastBlock Xh yt) = 0 ∧
          y = yt + ∑ κ, lam κ • blockShift Xh yt κ ∧
          ∀ a b, (bipGraph (Xmat Xh yt)).connectedComponentMk (Sum.inl a) ≠
              (bipGraph (Xmat Xh yt)).connectedComponentMk (Sum.inr b) → Ymat Xh y a b ≤ 0} ∧
      ∃ (m : ℕ) (g : Fin m → Dual n) (h : Fin m → ℝ),
        equivClass Xh yt = {y | ∀ i, inner ℝ (g i) y ≤ h i} := by sorry

end NearestDSM
