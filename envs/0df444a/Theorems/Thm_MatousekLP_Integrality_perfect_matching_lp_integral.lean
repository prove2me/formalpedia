-- Prove2me | Theorems.Thm_MatousekLP_Integrality_perfect_matching_lp_integral
-- name    : MatousekLP.Integrality.perfect_matching_lp_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:28:59.233808+00:00
-- url     : https://prove2.me/theorems/c42e0272-af45-4891-a160-0f4676729b67
-- title:
--   Theorem 3.2.1 — integrality of the bipartite perfect-matching LP relaxation
-- statement:
--   Let $G = (V, E)$ be an arbitrary finite bipartite graph with real edge weights $w_e$ (of any sign). Consider the LP relaxation of the perfect-matching integer program (3.1):
--   $$
--   \text{maximize } \sum_{e \in E} w_e x_e \quad \text{subject to } \sum_{e \in E:\, v \in e} x_e = 1 \ (v \in V), \quad 0 \le x_e \le 1 \ (e \in E).
--   $$
--   If this LP relaxation has at least one feasible solution, then it has at least one **integral** optimal solution $x$, i.e. $x_e \in \{0,1\}$ for every edge and $\sum_e w_e x_e \ge \sum_e w_e y_e$ for every feasible $y$ of the relaxation. This $x$ is an optimal solution for the integer program (3.1) as well.
--
--   The theorem says that a maximum-weight perfect matching of a bipartite graph can be found by solving a linear program. It does not assert that every optimal solution of the relaxation is integral.
--
--   **Formalization Note** The conclusion is a vector $x$ feasible for (3.1) (hence 0/1) that is optimal among all feasible points of the relaxation, and also, explicitly, among all feasible points of (3.1).
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 34, Theorem 3.2.1 (integer program (3.1): p. 33)

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_MatousekLP_Integrality_PerfectMatchingLP

namespace MatousekLP.Integrality

theorem perfect_matching_lp_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsBipartite G) (w : G.edgeSet → ℝ)
    (hfeas : ∃ x : G.edgeSet → ℝ, IsPMRelaxFeasible G x) :
    ∃ x : G.edgeSet → ℝ, IsPMIntFeasible G x ∧
      (∀ y : G.edgeSet → ℝ, IsPMRelaxFeasible G y → pmObjective G w y ≤ pmObjective G w x) ∧
      (∀ y : G.edgeSet → ℝ, IsPMIntFeasible G y → pmObjective G w y ≤ pmObjective G w x) := by sorry

end MatousekLP.Integrality
