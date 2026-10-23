-- Prove2me | Theorems.Thm_KellerTrotter2017_thm5_9_degree_sum_faithful
-- name    : KellerTrotter2017.thm5_9_degree_sum_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:26:52.279888+00:00
-- url     : https://prove2.me/theorems/ebf3a363-902f-4a1b-9dd7-50d23339d9cf
-- title:
--   Theorem 5.9 — $\sum_v \deg(v) = 2|E|$
-- statement:
--   Let $G = (V, E)$ be a finite simple graph and $\deg_G(v)$ the degree of the vertex $v$. Then
--
--   $$\sum_{v \in V} \deg_G(v) = 2|E|.$$
--
--   This is Theorem 5.9 of Keller and Trotter, *Applied Combinatorics*, the first counting fact of the graph theory chapter; it implies Corollary 5.10.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 74, Theorem 5.9

import Mathlib

theorem KellerTrotter2017.thm5_9_degree_sum_faithful {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by sorry
