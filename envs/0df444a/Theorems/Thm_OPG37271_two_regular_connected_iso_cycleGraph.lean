-- Prove2me | Theorems.Thm_OPG37271_two_regular_connected_iso_cycleGraph
-- name    : OPG37271.two_regular_connected_iso_cycleGraph
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:16:15.334054+00:00
-- url     : https://prove2.me/theorems/ad6ca3de-2076-472d-a2c7-8707bf7adf55
-- title:
--   Structure of Finite Connected 2-Regular Simple Graphs as Cycle Graphs
-- statement:
--   Every nonempty finite connected $2$-regular simple graph $H$ has at least $3$ vertices and is isomorphic to the standard cycle graph $C_{|W|}$ on $\mathrm{Fin}\,|W|$.
-- source:
--   Standard structural classification of 2-factors into disjoint cycles, used in Dvořák, Mohar, and Šámal (2013), Section 4.

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps

universe u
namespace OPG37271

theorem two_regular_connected_iso_cycleGraph
    {W : Type u} [Fintype W] (H : SimpleGraph W)
    (hne : Nonempty W) (hconn : H.Connected)
    (hreg : ∀ w : W, (H.neighborSet w).encard = 2) :
    3 ≤ Fintype.card W ∧
    Nonempty (H ≃g SimpleGraph.fromRel
      (fun i j : Fin (Fintype.card W) => (i.val + 1) % Fintype.card W = j.val)) := by sorry
end OPG37271
