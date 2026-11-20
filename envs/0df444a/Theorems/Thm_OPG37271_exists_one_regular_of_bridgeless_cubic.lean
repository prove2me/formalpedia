-- Prove2me | Theorems.Thm_OPG37271_exists_one_regular_of_bridgeless_cubic
-- name    : OPG37271.exists_one_regular_of_bridgeless_cubic
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:16:15.677721+00:00
-- url     : https://prove2.me/theorems/2f9341d0-8bed-418a-b600-d1dfbb957b7b
-- title:
--   Existence of a 1-Regular Spanning Subgraph in Finite Bridgeless Cubic Graphs
-- statement:
--   Every finite bridgeless $3$-regular simple graph $G$ contains a $1$-regular spanning subgraph $M \le G$ (whose complement $G \setminus E(M)$ is a $2$-factor).
-- source:
--   Julius Petersen, Acta Mathematica 15 (1891), 193–220; used in Dvořák, Mohar, and Šámal (2013), Proof of Theorem 4.1(a).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem exists_one_regular_of_bridgeless_cubic
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hcubic : ∀ v : V, (G.neighborSet v).encard = 3)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v) :
    ∃ M : SimpleGraph V, M ≤ G ∧ ∀ v : V, (M.neighborSet v).encard = 1 := by sorry
end OPG37271
