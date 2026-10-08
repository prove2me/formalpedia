-- Prove2me | Theorems.Thm_MatousekLP_Scheduling_support_subgraph_edges_le
-- name    : MatousekLP.Scheduling.support_subgraph_edges_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:39:28.45366+00:00
-- url     : https://prove2.me/theorems/f55e010e-c314-43bd-b1b0-1105376dba4b
-- title:
--   Lemma 8.3.2 — subgraphs of the support graph have no more edges than vertices
-- statement:
--   Let $d_{ij} > 0$ be running times of $n$ jobs on $m$ machines, let $T \in \mathbb{R}$, and let $(t, x)$ be an optimal solution of the linear program $\mathrm{LPR}(T)$ that satisfies Assumption 8.3.1 (the columns of the constraint matrix belonging to the nonzero $x_{ij}$ are linearly independent). Let $G = (M \cup J, E)$ with $E = \{\{i,j\} : x_{ij} > 0\}$ be the support graph of $x$.
--
--   Then every subgraph of $G$ has at most as many edges as vertices: if $M' \subseteq M$, $J' \subseteq J$ and $E' \subseteq E$ is a set of edges each joining a machine of $M'$ to a job of $J'$, then
--   $$
--   |E'| \le |M'| + |J'| .
--   $$
--
--   This counting property is what makes the support of a basic optimal solution sparse enough to be rounded: it forces the graph to be a forest with at most one extra edge per component.
--
--   **Formalization Note** A subgraph is given by vertex sets `M' : Finset (Fin m)`, `J' : Finset (Fin n)` and an edge set `E' ⊆ supportEdges x` whose pairs `(i, j)` satisfy `i ∈ M'` and `j ∈ J'`; this covers both deleting edges and deleting vertices with their incident edges. The standing assumption $d_{ij} > 0$ of Section 8.3 is a hypothesis.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 152, Lemma 8.3.2

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_MatousekLP_Scheduling_LPRelaxation

namespace MatousekLP.Scheduling

/-- Lemma 8.3.2 (Matoušek–Gärtner, p. 152). Let `(t, x)` be an optimal solution of
`LPR(T)` satisfying Assumption 8.3.1, and let `G = (M ∪ J, E)` be its support graph,
`E = {{i, j} : x_ij > 0}`. In any subgraph of `G` — a set `M'` of machines, a set
`J'` of jobs, and a set `E' ⊆ E` of edges joining `M'` to `J'` — the number of
edges is at most the number of vertices. -/
theorem support_subgraph_edges_le {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (T t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ)
    (hopt : LPROptimal d T t x) (hA : Assumption831 d T x)
    (M' : Finset (Fin m)) (J' : Finset (Fin n)) (E' : Finset (Fin m × Fin n))
    (hE'E : E' ⊆ supportEdges x) (hE'V : ∀ e ∈ E', e.1 ∈ M' ∧ e.2 ∈ J') :
    E'.card ≤ M'.card + J'.card := by sorry

end MatousekLP.Scheduling
