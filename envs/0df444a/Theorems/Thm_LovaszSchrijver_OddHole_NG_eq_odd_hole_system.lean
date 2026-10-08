-- Prove2me | Theorems.Thm_LovaszSchrijver_OddHole_NG_eq_odd_hole_system
-- name    : LovaszSchrijver.OddHole.NG_eq_odd_hole_system
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:50:32.751666+00:00
-- url     : https://prove2.me/theorems/0c4881d3-1140-4b56-8498-218f6e100a7d
-- title:
--   Theorem 2.3 — N(G) is exactly the solution set of the nonnegativity, edge, and odd hole constraints
-- statement:
--   Let $G = (V, E)$ be a finite graph with no isolated nodes, and let $N(G) = \{x \in \mathbb{R}^V : (1, x) \in N(\mathrm{FR}(G))\}$ be the relaxation of the stable set polytope obtained by one round of the Lovász–Schrijver operator $N$ applied to the fractional stable set polytope $\mathrm{FRAC}(G)$. Then $N(G)$ is exactly the set of $x \in \mathbb{R}^V$ satisfying
--
--   1. the nonnegativity constraints $x_i \ge 0$ for each $i \in V$;
--   2. the edge constraints $x_i + x_j \le 1$ for each $ij \in E$;
--   3. the odd hole constraints: for every set $C \subseteq V$ inducing a chordless odd cycle in $G$,
--   $$\sum_{i \in C} x_i \le \tfrac12(|C| - 1).$$
--
--   The theorem characterizes completely the constraints obtained in one step of the $N$ operator without positive semidefiniteness: one round of $N$ on $\mathrm{FRAC}(G)$ adds exactly the odd hole constraints. In particular $N(G) = \mathrm{STAB}(G)$ for every $t$-perfect graph.
--
--   **Formalization Note** Odd holes include triangles ($|C| = 3$) and exclude cycles with chords. The graph is assumed to have no isolated nodes, the paper's standing assumption in Section 2.a.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 178, Theorem 2.3

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
import Definitions.Def_LovaszSchrijver_OddHole_OddHole

namespace LovaszSchrijver.OddHole

/-- Theorem 2.3 (p. 178): for a finite graph `G` with no isolated nodes, the polytope `N(G)` is
exactly the solution set of the nonnegativity, edge, and odd hole constraints. -/
theorem NG_eq_odd_hole_system {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) :
    NG G = {x : V → ℝ | (∀ i, 0 ≤ x i) ∧ (∀ i j, G.Adj i j → x i + x j ≤ 1) ∧
      ∀ C : Finset V, IsOddHole G C → ∑ i ∈ C, x i ≤ ((C.card : ℝ) - 1) / 2} := by sorry

end LovaszSchrijver.OddHole
