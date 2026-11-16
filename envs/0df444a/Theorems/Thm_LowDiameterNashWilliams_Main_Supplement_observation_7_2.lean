-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_observation_7_2
-- name    : LowDiameterNashWilliams.Main.Supplement.observation_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:36:16.507195+00:00
-- url     : https://prove2.me/theorems/55752534-10d3-4799-b795-967c3fdc9e6d
-- title:
--   Observation 7.2 (used in the proof of Theorem 5; also used in Theorem 7) — Spanning double stars
-- statement:
--   Let $k\ge1$ and let a finite clique contain $k$ pairwise disjoint designated vertex pairs $(x_i,y_i)$. Additional clique vertices are permitted. There exist $k$ pairwise edge-disjoint spanning trees $F_i$ such that
--   $$x_iy_i\in E(F_i),\qquad \deg_{F_i}(v)=1\quad(v\notin\{x_i,y_i\}).$$
--   These double stars are the clique components used in both graph reductions.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: k disjoint designated pairs with arbitrary extra vertices → an embedding of Fin k × Bool into the vertex labels; reason: the embedding states distinctness but imposes no exhaustiveness condition
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Observation 7.2, p. 26 (PDF p. 27)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_GraphEncoding

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem observation_7_2 (k : ℕ) (hk : 1 ≤ k) (G : GraphInput) (hG : IsClique G)
    (labels : (Fin k × Bool) ↪ Fin G.n) :
    ∃ T : Trees k G.m, Packing G.ends T ∧ ∀ i : Fin k,
      (∃ e ∈ T i, G.ends e = s(labels (i,false), labels (i,true))) ∧
      ∀ v : Fin G.n, v ≠ labels (i,false) → v ≠ labels (i,true) →
        degIn G.ends (T i) v = 1 := by sorry

end LowDiameterNashWilliams.Main.Supplement
