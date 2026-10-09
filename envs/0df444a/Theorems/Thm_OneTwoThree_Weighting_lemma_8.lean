-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_8
-- name    : OneTwoThree.Weighting.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:36.38885+00:00
-- url     : https://prove2.me/theorems/aaddfc19-dcf0-41a8-8dcd-fd1d40e9970f
-- title:
--   Lemma 8 — a good R-B-partition of $G[V\setminus\{v_0\}]$ with $\deg_R(v_0)\ge 2$ yields a vertex-coloring weighting of $G$
-- statement:
--   Let $G=(V,E)$ be a finite graph and $v_0\in V$ a vertex such that the induced subgraph $G[V\setminus\{v_0\}]$ is connected. Let $(R,B)$ be a good R-B-partition of $G[V\setminus\{v_0\}]$, and write $\deg_W(v_0)=|N(v_0)\cap W|$. Suppose that
--   $$\deg_R(v_0)\ge 2\qquad\text{and}\qquad \deg_R(v_0)\ \text{is even or}\ \deg_B(v_0)\ge 1.$$
--   Then there exists a vertex-coloring edge-weighting $\omega:E\to\{1,2,3\}$ of $G$.
--
--   This is the second basic situation of the proof of Theorem 1: one extra vertex outside the good partition with at least two red neighbours.
--
--   **Formalization Note** A good R-B-partition of $G[V\setminus\{v_0\}]$ is `IsGoodPartition G {v₀}ᶜ R B`: $R$, $B$ partition $V\setminus\{v_0\}$, and independence and the bipartite graph $G(R,B)$ are taken in $G$, which agrees with the induced subgraph since $v_0\notin R\cup B$.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 8, Lemma 8

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_8 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v₀ : V) (hconn : (G.induce ({v₀}ᶜ : Set V)).Connected)
    (R B : Finset V) (hRB : IsGoodPartition G {v₀}ᶜ R B)
    (h2 : 2 ≤ #(G.neighborFinset v₀ ∩ R))
    (hpar : Even #(G.neighborFinset v₀ ∩ R) ∨ 1 ≤ #(G.neighborFinset v₀ ∩ B)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧ IsVertexColoring G ω := by sorry

end OneTwoThree.Weighting
