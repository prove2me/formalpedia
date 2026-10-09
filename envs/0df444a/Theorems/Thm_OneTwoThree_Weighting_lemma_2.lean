-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_2
-- name    : OneTwoThree.Weighting.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:46.373022+00:00
-- url     : https://prove2.me/theorems/37af1cac-1e56-445b-908f-e183cf6d3aa1
-- title:
--   Lemma 2 — an independent set $R$ with $G(R,V\setminus R)$ connected, alternating along a shortest path
-- statement:
--   Let $G=(V,E)$ be a finite connected graph, let $v,w\in V$, and let $p=(v_1=v,v_2,\dots,v_k=w)$ be a shortest $v$-$w$-path in $G$. Then for each of the two choices "$v\in R$" and "$v\notin R$" there exists an independent set $R\subseteq V$ realizing that choice such that
--
--   1. the bipartite graph $G(R,V\setminus R)$, whose edges are the edges of $G$ between $R$ and $V\setminus R$, is connected, and
--   2. the path $p$ alternates between $R$ and $V\setminus R$: for every $i<k$,
--   $$v_i\in R\iff v_{i+1}\notin R.$$
--
--   The lemma supplies the red/blue vertex partition on which the whole construction is built.
--
--   **Formalization Note** The path is a walk `p : G.Walk v w` whose length equals the graph distance (which makes it a path). Its $i$-th vertex is `p.getVert i` (indexed from $0$). The choice of side for $v$ is a Boolean `b`, quantified before the existential: for every `b` there is an `R` with `v ∈ R ↔ b = true`. Since $R\cup(V\setminus R)=V$, connectivity of $G(R,V\setminus R)$ is connectivity of a graph on all of $V$.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 3, Lemma 2

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) {v w : V} (p : G.Walk v w) (hp : p.length = G.dist v w) (b : Bool) :
    ∃ R : Finset V, G.IsIndepSet (R : Set V) ∧
      (G.between (R : Set V) (R : Set V)ᶜ).Connected ∧
      (∀ i < p.length, (p.getVert i ∈ R ↔ p.getVert (i + 1) ∉ R)) ∧
      (v ∈ R ↔ b = true) := by sorry

end OneTwoThree.Weighting
