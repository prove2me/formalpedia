-- Prove2me | Theorems.Thm_LovaszSchrijver_OddHole_mem_NG_iff_matrix_system
-- name    : LovaszSchrijver.OddHole.mem_NG_iff_matrix_system
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:49:20.240912+00:00
-- url     : https://prove2.me/theorems/69127d82-1697-4a44-b170-37a96aa2ac97
-- title:
--   Proof of Theorem 2.3, part (2) — membership in N(G) as a system on the entries of Y
-- statement:
--   Let $G = (V, E)$ be a finite graph with no isolated nodes and let $x \in \mathbb{R}^V$. Then $x \in N(G)$ if and only if there exists a symmetric matrix $Y = (y_{ij})$ with rows and columns indexed by $V \cup \{0\}$ such that
--
--   1. every entry of $Y$ is nonnegative;
--   2. $y_{00} = 1$ and $y_{i0} = y_{ii} = x_i$ for all $i \in V$;
--   3. for all $i, j, k \in V$ with $ij \in E$,
--   $$x_i + x_j + x_k - 1 \le y_{ik} + y_{jk} \le x_k.$$
--
--   In the paper the lower bound comes from the condition that $Yf_k \in \mathrm{FR}(G)$ with $f_k = e_0 - e_k$, and the upper bound from $Ye_k \in \mathrm{FR}(G)$. The proof of Theorem 2.3 uses the direction "$\Leftarrow$": to show that a point satisfying the nonnegativity, edge and odd hole constraints lies in $N(G)$, it suffices to solve this system, which Lemma 2.4 handles.
--
--   **Formalization Note** The page states only the direction it needs; the equivalence is stated. The direction "$\Leftarrow$" uses that $G$ has no isolated nodes (a neighbour of $k$ gives $y_{ik} \le x_i$).
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 178, part (2) of the proof of Theorem 2.3

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones

namespace LovaszSchrijver.OddHole

/-- Proof of Theorem 2.3, part (2) (p. 178): `x ∈ N(G)` if and only if there is a nonnegative
symmetric `(n+1) × (n+1)` matrix `Y` with `y_{i0} = y_{ii} = x_i`, `y_{00} = 1`, and
`x_i + x_j + x_k − 1 ≤ y_{ik} + y_{jk} ≤ x_k` for all `i, j, k ∈ V` with `ij ∈ E`. -/
theorem mem_NG_iff_matrix_system {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) (x : V → ℝ) :
    x ∈ NG G ↔ ∃ Y : Matrix (Option V) (Option V) ℝ,
      (∀ p q, 0 ≤ Y p q) ∧ Y.IsSymm ∧ Y none none = 1 ∧
      (∀ i, Y (some i) none = x i ∧ Y (some i) (some i) = x i) ∧
      ∀ i j k, G.Adj i j →
        x i + x j + x k - 1 ≤ Y (some i) (some k) + Y (some j) (some k) ∧
        Y (some i) (some k) + Y (some j) (some k) ≤ x k := by sorry

end LovaszSchrijver.OddHole
