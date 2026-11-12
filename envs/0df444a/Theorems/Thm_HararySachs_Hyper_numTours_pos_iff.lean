-- Prove2me | Theorems.Thm_HararySachs_Hyper_numTours_pos_iff
-- name    : HararySachs.Hyper.numTours_pos_iff
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T03:35:21.015619+00:00
-- url     : https://prove2.me/theorems/4ffe8be5-6bf8-4b39-a8b5-cafc8e2e5427
-- title:
--   Euler's criterion — a digraph has an Euler tour iff it is Eulerian
-- statement:
--   This is Euler's criterion for directed multigraphs, in the form used in the proof of Lemma 4 of Clark and Cooper: a digraph has an Euler tour exactly when it is Eulerian.
--
--   Let $D$ be a directed multigraph on $[n]$ with $m(u,v)$ distinguishable arcs from $u$ to $v$ (loops allowed) and $L=\sum_{u,v}m(u,v)>0$ arcs in total. Call $D$ *Eulerian* when the following hold, where $V(D)$ is the set of vertices of positive degree:
--
--   1. $V(D)\neq\emptyset$;
--   2. $\deg^+(v)=\deg^-(v)$ for every vertex $v$;
--   3. any two vertices of $V(D)$ are joined by a chain of arcs, each traversed in either direction.
--
--   Then
--
--   $$
--   D \text{ has an Euler tour} \iff D \text{ is Eulerian}.
--   $$
--
--   An Euler tour is a closed trail using every arc exactly once, with a distinguished first position.
--
--   The paper recalls this criterion on p. 5 before Lemma 4. It is the existence half of Lemma 4, and every Euler-circuit count, such as the BEST theorem, presupposes it.
--
--   **Formalization Note** The left-hand side is `0 < numTours m hL`, the number of tour bijections `Fin L ≃ Arcs m`. Eulerian is the mission predicate `IsEulerian m`, with weak connectivity expressed by `Relation.ReflTransGen (WeakAdjacent m)` on active vertices.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 5, paragraph after Definition 4 ('a digraph D has an Euler circuit if and only if deg+(v) = deg−(v) for all v ∈ V(D) and D is weakly connected'), used in the proof of Lemma 4, p. 6

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators

namespace HararySachs.Hyper

theorem numTours_pos_iff {n L : ℕ} (hL : 0 < L) (m : ArcMult n)
    (hm : (∑ u : Fin n, ∑ v : Fin n, m u v) = L) :
    0 < numTours m hL ↔ IsEulerian m := by sorry

end HararySachs.Hyper
