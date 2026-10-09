-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_theorem_1
-- name    : OneTwoThree.Weighting.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:47.132186+00:00
-- url     : https://prove2.me/theorems/4c03db1f-07a9-40f5-b041-71fae701f2ab
-- title:
--   Theorem 1 — every graph without a $K_2$ component has a vertex-coloring edge-weighting with weights $\{1,2,3\}$
-- statement:
--   **The 1-2-3 Conjecture (Karoński, Łuczak, Thomason 2004), proved by Keusch.** Let $G=(V,E)$ be a finite graph none of whose connected components is isomorphic to $K_2$ (a single edge). Then there exists an edge-weighting $\omega:E\to\{1,2,3\}$ such that for each edge $\{v,w\}\in E$,
--   $$\sum_{u\in N(v)}\omega(\{u,v\})\ \ne\ \sum_{u\in N(w)}\omega(\{u,w\}).$$
--
--   In words: the edges can be weighted with $1$, $2$ and $3$ so that adjacent vertices always receive different sums of incident weights. The hypothesis is necessary, because the two ends of an isolated edge always receive the same sum. The bound $3$ cannot be lowered to $2$ in general.
--
--   **Formalization Note** The vertex type is finite; the paper's "graph" is a finite simple graph (weighted degrees are finite sums, and the proof uses a maximum cut and vertex orderings). The weighting is a function on unordered pairs required to take values in $\{1,2,3\}$ on edges only (`IsWeighting G 3`). The weighted degree is the sum over the neighbourhood (`wdeg`); because $\{u,v\}=\{v,u\}$ it equals each side of the displayed inequality, so the conclusion is that $\omega$ is vertex-coloring (`IsVertexColoring`). "No component isomorphic to $K_2$" is stated with Mathlib's connected components and graph isomorphisms; it is equivalent to "no edge both of whose ends have degree $1$".
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 2, Theorem 1 (published: J. Combin. Theory Ser. B, 2024, DOI 10.1016/j.jctb.2024.01.002)

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem theorem_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : NoK2Component G) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧ IsVertexColoring G ω := by sorry

end OneTwoThree.Weighting
