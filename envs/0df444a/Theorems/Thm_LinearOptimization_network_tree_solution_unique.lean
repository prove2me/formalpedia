-- Prove2me | Theorems.Thm_LinearOptimization_network_tree_solution_unique
-- name    : LinearOptimization.network_tree_solution_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T21:59:37.132726+00:00
-- url     : https://prove2.me/theorems/5a25b729-6c2c-4ca7-8749-29fc33b86299
-- title:
--   Existence and uniqueness of the tree solution
-- statement:
--   **(Bertsimas & Tsitsiklis, Theorem 7.3, p. 281)** Let $T\subset\mathcal{A}$ be a set of $n-1$ arcs that form a tree when their direction is ignored. Then, the system of linear equations $\tilde{\mathbf{A}}\mathbf{f}=\tilde{\mathbf{b}}$, and $f_{ij}=0$ for all $(i,j)\notin T$, has a unique solution.
--
--   (The book's proof: the $(n-1)\times(n-1)$ matrix $\mathbf{B}$ of the $T$-columns of $\tilde{\mathbf{A}}$ can be reordered to lower-triangular form with nonzero diagonal, hence is nonsingular — so the $n-1$ columns of $\tilde{\mathbf{A}}$ associated with the tree arcs form a basis.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 7.3, p. 281

import Definitions.Def_LinearOptimization_TreeSolution


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 7.3 (p. 281).** For a set `T` of arcs forming a tree
when direction is ignored (on `n + 1` nodes, so `T` has `n` arcs), the
system `Ãf = b̃` together with `f_k = 0` for all `k ∉ T` has a unique
solution. -/

theorem LinearOptimization.network_tree_solution_unique {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1)) (bsupply : Fin (n + 1) → ℝ)
    (hloop : HasNoSelfLoops arcs)
    (T : Finset (Fin m)) (hT : IsTreeArcSet arcs T) :
    ∃! f : Fin m → ℝ,
      (truncatedIncidence arcs).mulVec f = truncatedSupply bsupply ∧
      ∀ k, k ∉ T → f k = 0 := by
  sorry
