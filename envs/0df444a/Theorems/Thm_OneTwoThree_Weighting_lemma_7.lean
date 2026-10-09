-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_7
-- name    : OneTwoThree.Weighting.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:29.249171+00:00
-- url     : https://prove2.me/theorems/7fd26f40-f4be-4ba9-b2c0-288a0592d592
-- title:
--   Lemma 7 — a good R-B-partition of $G$ yields a vertex-coloring $\{1,2,3\}$-weighting, even exactly on $R$
-- statement:
--   Let $G=(V,E)$ be a finite connected graph and let $(R,B)$ be a good R-B-partition of $G$: $V=R\cup B$ disjointly, $R$ is independent, $G(R,B)$ is connected and $|B|$ is even. Then there exists an edge-weighting $\omega:E\to\{1,2,3\}$ such that the weighted degrees $s_\omega$ form a proper vertex coloring of $G$ and, for every vertex $v$,
--   $$s_\omega(v)\ \text{is even}\iff v\in R.$$
--
--   This is the first of the three basic situations to which the proof of Theorem 1 reduces every graph.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 8, Lemma 7

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (R B : Finset V)
    (hRB : IsGoodPartition G univ R B) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧ IsVertexColoring G ω ∧
      ∀ v, Even (wdeg G ω v) ↔ v ∈ R := by sorry

end OneTwoThree.Weighting
