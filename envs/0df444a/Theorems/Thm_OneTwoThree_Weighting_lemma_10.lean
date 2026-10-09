-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_10
-- name    : OneTwoThree.Weighting.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:35.412302+00:00
-- url     : https://prove2.me/theorems/fb609383-d8c9-48d1-9be7-ddd79d2ac578
-- title:
--   Lemma 10 — a connected graph of minimum degree $\ge 2$ has an edge $\{x,y\}$ with $G[V\setminus\{x,y\}]$ connected
-- statement:
--   Let $G=(V,E)$ be a finite connected graph with minimum degree at least $2$. Then there exist two vertices $x,y\in V$ such that $\{x,y\}\in E$ and the induced subgraph
--   $$G[V\setminus\{x,y\}]$$
--   is connected.
--
--   In the proof of Theorem 1 this non-separating edge is the starting point of the case analysis for graphs without vertices of degree one.
--
--   **Formalization Note** Mathlib's `Connected` requires a nonempty vertex set. Minimum degree at least $2$ forces $|V|\ge 3$, so $V\setminus\{x,y\}$ is nonempty and the conclusion asks for genuine connectivity.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 11, Lemma 10

import Mathlib

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (hdeg : ∀ v, 2 ≤ G.degree v) :
    ∃ x y : V, G.Adj x y ∧ (G.induce ({x, y}ᶜ : Set V)).Connected := by sorry

end OneTwoThree.Weighting
