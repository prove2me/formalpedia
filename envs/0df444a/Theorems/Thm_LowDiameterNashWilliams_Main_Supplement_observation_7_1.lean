-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_observation_7_1
-- name    : LowDiameterNashWilliams.Main.Supplement.observation_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:35:44.879907+00:00
-- url     : https://prove2.me/theorems/0c30d0ae-85ad-4be1-970d-ab4f98a3c752
-- title:
--   Observation 7.1 (used in the proof of Theorem 5) — Shallow clique packing
-- statement:
--   Let $k\ge1$. In the complete graph on distinct vertices $r,a_1,b_1,\ldots,a_k,b_k$, there exist $k$ pairwise edge-disjoint spanning trees $H_1,\ldots,H_k$ such that, for every $i$,
--   $$\operatorname{depth}_r(H_i)\le2,\qquad N_{H_i}(r)=\{a_i,b_i\}.$$
--   The neighbor set is exact. This gives the shallow clique trees used in the rooted hardness construction.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: distinct labelled root and k pairs exhaust the clique → an equivalence from Option (Fin k × Bool) onto the vertices; reason: this states exactly the distinctness and exhaustiveness, without extra clique vertices
--   - encoding: shortest-path lengths, rooted depth and diameter measured in edges → published extended nonnegative distances, with depth and diameter taken by finite suprema; reason: on the connected graphs and spanning trees in these statements these values are the finite source values; disconnected pairs have infinite distance
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Observation 7.1, p. 26 (PDF p. 27)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_GraphEncoding

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem observation_7_1 (k : ℕ) (hk : 1 ≤ k) (G : GraphInput) (hG : IsClique G)
    (labels : Option (Fin k × Bool) ≃ Fin G.n) :
    ∃ T : Trees k G.m, Packing G.ends T ∧ ∀ i : Fin k,
      depth G.ends (T i) (labels none) ≤ 2 ∧
      ∀ v : Fin G.n, (edgeGraph G.ends (T i)).Adj (labels none) v ↔
        v = labels (some (i,false)) ∨ v = labels (some (i,true)) := by sorry

end LowDiameterNashWilliams.Main.Supplement
