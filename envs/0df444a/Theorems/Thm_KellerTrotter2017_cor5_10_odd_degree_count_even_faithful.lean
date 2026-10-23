-- Prove2me | Theorems.Thm_KellerTrotter2017_cor5_10_odd_degree_count_even_faithful
-- name    : KellerTrotter2017.cor5_10_odd_degree_count_even_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:26:51.77786+00:00
-- url     : https://prove2.me/theorems/742c054c-7e5f-4e85-a073-8014e37ab638
-- title:
--   Corollary 5.10 — an even number of vertices have odd degree
-- statement:
--   Let $G = (V, E)$ be a finite simple graph. Then the number of vertices $v$ with $\deg_G(v)$ odd is even:
--
--   $$\#\{v \in V : \deg_G(v) \text{ odd}\} \equiv 0 \pmod 2.$$
--
--   This is Corollary 5.10 of Keller and Trotter, *Applied Combinatorics*, a consequence of Theorem 5.9.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 74, Corollary 5.10

import Mathlib

theorem KellerTrotter2017.cor5_10_odd_degree_count_even_faithful {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Finset.univ.filter (fun v => Odd (G.degree v))).card := by sorry
