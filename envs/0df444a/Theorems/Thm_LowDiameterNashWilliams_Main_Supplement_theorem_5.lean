-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_theorem_5
-- name    : LowDiameterNashWilliams.Main.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:38:53.670374+00:00
-- url     : https://prove2.me/theorems/79db437c-05fa-42c4-b76b-a3b62bde7166
-- title:
--   Theorem 5 (companion theorem; not used in the proof of the goal) — Exact diameter-threshold hardness
-- statement:
--   For every fixed integer $k\ge2$, it is NP-hard, given an $n$-vertex finite simple graph $G$ promised to have $k$ pairwise edge-disjoint spanning trees, to decide whether it has such a packing satisfying
--   $$\operatorname{diam}(T_i)\le\frac{n}{2\delta(G)}\qquad(i\in[k]),$$
--   where $\delta(G)$ is minimum degree. NO is nonexistence of this packing within the same promise. The reduction and its polynomial may depend on fixed $k$, while the input graph varies. This is an independent companion to the main existence theorem.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: diameter and minimum-degree ratios on the graph packing promise → at least two vertices in each graph hardness promise; reason: these are the nondegenerate inputs on which the source ratios are defined; the promise then implies positive minimum degree
--   - encoding: NP-hardness for every fixed parameter → GapNPHard of explicit self-delimiting binary input codes using CookPvsNP polynomial-time machines; reason: this is polynomial-time many-one promise hardness; all validity constraints occur on both output sides and reductions may depend on the fixed parameter
--   - encoding: shortest-path lengths, rooted depth and diameter measured in edges → published extended nonnegative distances, with depth and diameter taken by finite suprema; reason: on the connected graphs and spanning trees in these statements these values are the finite source values; disconnected pairs have infinite distance
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Theorem 5, p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_Promises

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn
open SetCoverThreshold.SetCover

namespace LowDiameterNashWilliams.Main.Supplement

theorem theorem_5 (k : ℕ) (hk : 2 ≤ k) :
    GapNPHard GraphInput.encode (DiameterYes k) (DiameterNo k) := by sorry

end LowDiameterNashWilliams.Main.Supplement
