-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_connected_case
-- name    : OneTwoThree.Weighting.connected_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:28.578224+00:00
-- url     : https://prove2.me/theorems/02c9e139-e6b9-4660-9e4d-2016b32ca690
-- title:
--   §3, p. 14 — the connected case: every connected graph on at least 3 vertices has a vertex-coloring $\{1,2,3\}$-weighting
-- statement:
--   Let $G=(V,E)$ be a finite connected graph with $|V|\ge 3$. Then there exists an edge-weighting $\omega:E\to\{1,2,3\}$ such that for every edge $\{v,w\}\in E$
--   $$s_\omega(v)\ne s_\omega(w).$$
--
--   This is the conclusion of the case analysis in the proof of Theorem 1 (pp. 11–14), stated in the last sentence of that proof. The proof begins by assuming without loss of generality that $G$ is connected with at least three vertices; Theorem 1 follows by treating each connected component separately, since components with one vertex have no edges.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 14, §3, proof of Theorem 1, last sentence (with the reduction on p. 11: "Assume w.l.o.g. that G is connected and contains at least three vertices.")

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem connected_case {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (hV : 3 ≤ Fintype.card V) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧ IsVertexColoring G ω := by sorry

end OneTwoThree.Weighting
