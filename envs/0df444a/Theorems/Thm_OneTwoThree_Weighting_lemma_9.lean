-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_9
-- name    : OneTwoThree.Weighting.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:34.102502+00:00
-- url     : https://prove2.me/theorems/5808bb45-2962-4f1b-a71f-ef4052d1eb23
-- title:
--   Lemma 9 — one red neighbour $u_0$ and a blue-to-blue path avoiding $u_0$ yield a vertex-coloring weighting
-- statement:
--   Let $G=(V,E)$ be a finite graph and $v_0\in V$ a vertex such that $G[V\setminus\{v_0\}]$ is connected. Let $(R,B)$ be a good R-B-partition of $G[V\setminus\{v_0\}]$ and let $u_0\in R$ with
--   $$N(v_0)\cap R=\{u_0\}.$$
--   Suppose that there exists a non-trivial path in $G(R,B)$ that starts and ends in $N(v_0)\cap B$ and does not contain $u_0$. Then there exists an edge-weighting $\omega:E\to\{1,2,3\}$ whose weighted degrees form a proper vertex coloring of $G$.
--
--   This is the third basic situation of the proof of Theorem 1, where $v_0$ has a single red neighbour; the path is used to repair the one possible conflict between $v_0$ and $u_0$.
--
--   **Formalization Note** The path is a walk in Mathlib's `G.between R B` (edges of $G$ between $R$ and $B$) that is a path, has positive length ("non-trivial") and whose support avoids $u_0$; its two ends lie in $N(v_0)\cap B$. The graph `G.between R B` lives on all of $V$, but a walk between two vertices of $B$ stays inside $R\cup B$ because $v_0$ has no edges there, so it is a path of $G(R,B)$.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 10, Lemma 9

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v₀ : V) (hconn : (G.induce ({v₀}ᶜ : Set V)).Connected)
    (R B : Finset V) (hRB : IsGoodPartition G {v₀}ᶜ R B)
    (u₀ : V) (hu₀ : u₀ ∈ R) (hN : G.neighborFinset v₀ ∩ R = {u₀})
    (hpath : ∃ a b : V, a ∈ G.neighborFinset v₀ ∩ B ∧ b ∈ G.neighborFinset v₀ ∩ B ∧
      ∃ q : (G.between (R : Set V) (B : Set V)).Walk a b,
        q.IsPath ∧ 0 < q.length ∧ u₀ ∉ q.support) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧ IsVertexColoring G ω := by sorry

end OneTwoThree.Weighting
