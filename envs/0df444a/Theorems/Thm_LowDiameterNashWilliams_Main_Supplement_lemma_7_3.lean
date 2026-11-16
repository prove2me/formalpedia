-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_lemma_7_3
-- name    : LowDiameterNashWilliams.Main.Supplement.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:37:00.049683+00:00
-- url     : https://prove2.me/theorems/88851c87-662c-438d-bc24-ab051e4d026e
-- title:
--   Lemma 7.3 (used in the proof of Theorem 5) — Rooted depth-two packing is NP-hard
-- statement:
--   For every fixed integer $k\ge2$, consider a finite simple graph $G$ promised to contain $k$ pairwise edge-disjoint spanning trees and a specified root $r$. It is NP-hard to decide whether
--   $$\exists(T_i)_{i=1}^k\text{ an edge-disjoint spanning-tree packing},\quad\forall i,\ \operatorname{depth}_r(T_i)\le2.$$
--   YES is this existence predicate, and NO is its negation within the packing promise. The input supplies the graph and root alone. NP-hardness means an actual polynomial-time many-one map from every NP language; no hardness assumption is a hypothesis.
--
--   Differences from the source:
--   - encoding: finite simple unweighted graphs with unordered edges → labelled finite endpoint arrays with the published simplicity and spanning-tree predicates; reason: every finite graph is represented up to relabelling; each unordered edge is counted once
--   - encoding: NP-hardness for every fixed parameter → GapNPHard of explicit self-delimiting binary input codes using CookPvsNP polynomial-time machines; reason: this is polynomial-time many-one promise hardness; all validity constraints occur on both output sides and reductions may depend on the fixed parameter
--   - encoding: shortest-path lengths, rooted depth and diameter measured in edges → published extended nonnegative distances, with depth and diameter taken by finite suprema; reason: on the connected graphs and spanning trees in these statements these values are the finite source values; disconnected pairs have infinite distance
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 7.3, p. 26 (PDF p. 27)

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

theorem lemma_7_3 (k : ℕ) (hk : 2 ≤ k) :
    GapNPHard RootedInput.encode (DepthYes k) (DepthNo k) := by sorry

end LowDiameterNashWilliams.Main.Supplement
