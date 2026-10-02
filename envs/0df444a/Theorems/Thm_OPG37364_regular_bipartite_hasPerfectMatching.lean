-- Prove2me | Theorems.Thm_OPG37364_regular_bipartite_hasPerfectMatching
-- name    : OPG37364.regular_bipartite_hasPerfectMatching
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T09:00:15.821951+00:00
-- url     : https://prove2.me/theorems/a5ac2040-c769-40d8-bd27-c8e7e20b618c
-- title:
--   Finite regular bipartite graphs of positive degree have perfect matchings
-- statement:
--   Let $G$ be a finite simple bipartite graph, and let $d$ be a positive integer. If every vertex has exactly $d$ neighbors, then $G$ has a perfect matching.
--
--   Equivalently, there is a map $m:V(G)\to V(G)$ satisfying
--
--   $$v\sim_G m(v)\quad\text{and}\quad m(m(v))=v\qquad(v\in V(G)).$$
--
--   Adjacency in a simple graph excludes fixed points. Connectedness is not required. This standard consequence of Hall's marriage theorem supplies the final perfect-matching step in Lemma 5, including its degree-fourteen instance.
-- source:
--   The standard regular-bipartite consequence of Hall's Marriage Theorem, used in the final sentence of the proof of Lemma 5, Feghali--Lucke--Paulusma--Ries, Algorithmica 87 (2025), https://link.springer.com/article/10.1007/s00453-025-01318-8. Finite Hall infrastructure: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/Hall/Finite.lean

import Definitions.Def_opg37364_matching_cuts

set_option autoImplicit false

namespace OPG37364

universe u

theorem regular_bipartite_hasPerfectMatching {V : Type u} [Finite V]
    (G : SimpleGraph V) (d : ℕ) (hd : 0 < d)
    (hreg : IsRegularOfDegree G d) (hbip : IsBipartite G) :
    HasPerfectMatching G := by sorry

end OPG37364
